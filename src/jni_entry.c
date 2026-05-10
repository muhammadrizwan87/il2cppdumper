/**
 * @file jni_entry.c
 * @brief JNI entry point and background dump orchestration.
 *
 * This module is the bridge between the Android Java/Kotlin app and the
 * native IL2CPP dumper.  It performs three major tasks:
 *
 *   1. On library load (constructor attribute), spawn a detached thread that
 *      waits for `libil2cpp.so` to be mapped, resolves the IL2CPP API, and
 *      writes a `dump.cs` listing of all managed types.
 *   2. Expose a JNI call (`nativeStart`) that can be invoked from managed
 *      code to trigger the same dump on demand.
 *   3. Install a temporary `SIGSEGV` / `SIGBUS` handler on the dump thread
 *      to protect the host application from crashes during the memory scan.
 *
 * @section security Safe crash handling
 * The dump traverses IL2CPP internal data structures; if those structures are
 * corrupt or not yet initialised the process would normally crash.  We use
 * `sigsetjmp`/`siglongjmp` to gracefully abort the dump instead of killing
 * the whole application.
 */

#define _GNU_SOURCE
#define _POSIX_C_SOURCE 200809L

#include <jni.h>
#include <pthread.h>
#include <signal.h>
#include <setjmp.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/syscall.h>
#include <dlfcn.h>
#include <limits.h>

#include "log.h"
#include "il2cpp_api.h"
#include "il2cpp_dump.h"

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

/*
 * JNI naming helpers.
 *
 * pkg  : lower‑case native package segment  (e.g. com_il2cppapp).
 * cls  : Java class name           (Il2CppDumper).
 * fn   : native method name.
 *
 * The convention is Java_<pkg>_<cls>_<fn>.
 */
#define JAVA_PKG_NATIVE  com_il2cppapp_Il2CppDumper
#define _JNI_STR(pkg, cls, fn)  Java_ ## pkg ## _ ## cls ## _ ## fn
#define JNI_EXPORT(pkg, fn)     _JNI_STR(pkg, Il2CppDumper, fn)

/** Saved JVM pointer, obtained in JNI_OnLoad, used for JNIEnv retrieval. */
static JavaVM *g_jvm = NULL;

/* -------------------------------------------------------------------------
 * Crash‑safe dump execution
 * ------------------------------------------------------------------------- */
#define DUMP_SIGSTACK_SIZE 16384

/** Alternative signal stack for the crash handler. */
static uint8_t              g_sigstack[DUMP_SIGSTACK_SIZE];
/** Jump buffer for longjmp back to dump entry. */
static sigjmp_buf           g_crash_jmp;
/** Guard to prevent re‑entry into the crash handler. */
static volatile sig_atomic_t g_in_dump  = 0;
/** Saved previous SIGSEGV/SIGBUS actions (restored after dump). */
static struct sigaction     g_old_segv;
static struct sigaction     g_old_bus;

/**
 * @brief Signal handler installed during the dump.
 *
 * If the crash occurs while we are inside the dump (g_in_dump == 1),
 * we perform a siglongjmp back to the safe point in dump_thread().
 * Otherwise we forward the signal to the previously installed handler
 * or set it to default behaviour to avoid interfering with normal app
 * crashes.
 *
 * @param sig   signal number (SIGSEGV or SIGBUS).
 * @param si    additional signal info (unused).
 * @param ctx   CPU context (unused).
 */
static void crash_signal_handler(int sig, siginfo_t *si, void *ctx) {
    (void)si; (void)ctx;

    if (g_in_dump) {
        g_in_dump = 0;
        siglongjmp(g_crash_jmp, sig);   /* abort dump, return error */
    }

    /* Forward signal to original handler or restore default action. */
    struct sigaction *old = (sig == SIGSEGV) ? &g_old_segv : &g_old_bus;
    if (old->sa_flags & SA_SIGINFO) {
        old->sa_sigaction(sig, si, ctx);
    } else if (old->sa_handler != SIG_IGN && old->sa_handler != SIG_DFL) {
        old->sa_handler(sig);
    } else {
        signal(sig, SIG_DFL);
        raise(sig);
    }
}

/**
 * @brief Register the crash handler on an alternate stack.
 *
 * The alternate stack is necessary because a stack overflow could also
 * trigger SIGSEGV; with a dedicated stack the handler can still run.
 */
static void install_crash_handler(void) {
    /* Configure alternate signal stack */
    stack_t ss;
    ss.ss_sp    = g_sigstack;
    ss.ss_size  = sizeof(g_sigstack);
    ss.ss_flags = 0;
    sigaltstack(&ss, NULL);

    struct sigaction sa;
    memset(&sa, 0, sizeof(sa));
    sa.sa_sigaction = crash_signal_handler;
    sa.sa_flags     = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);

    sigaction(SIGSEGV, &sa, &g_old_segv);
    sigaction(SIGBUS,  &sa, &g_old_bus);
}

/**
 * @brief Restore original signal handlers and disable alternate stack.
 */
static void uninstall_crash_handler(void) {
    sigaction(SIGSEGV, &g_old_segv, NULL);
    sigaction(SIGBUS,  &g_old_bus,  NULL);

    /* Disable alternate stack */
    stack_t ss;
    ss.ss_flags = SS_DISABLE;
    ss.ss_sp    = g_sigstack;
    ss.ss_size  = sizeof(g_sigstack);
    sigaltstack(&ss, NULL);
}

/* -------------------------------------------------------------------------
 * Helper: mkdir -p
 * ------------------------------------------------------------------------- */
/**
 * @brief Create a directory tree (like `mkdir -p`).
 *
 * @param path Full path to create.
 */
static void mkdir_p(const char *path) {
    char   tmp[PATH_MAX];
    size_t len = strnlen(path, sizeof(tmp) - 1);
    if (!len || len >= sizeof(tmp)) return;
    memcpy(tmp, path, len);
    tmp[len] = '\0';
    char *p;
    for (p = tmp + 1; *p; ++p) {
        if (*p == '/') { *p = '\0'; mkdir(tmp, 0755); *p = '/'; }
    }
    mkdir(tmp, 0755);
}

/* -------------------------------------------------------------------------
 * Process / app identification
 * ------------------------------------------------------------------------- */
/**
 * @brief Read the process name from /proc/self/cmdline.
 *
 * The cmdline file contains the executable path, often with a trailing
 * colon (for Android apps: `com.example.app:`).  We extract the part
 * before the first colon / NUL as the package name.
 *
 * @param buf Output buffer (at least sz bytes).
 * @param sz  Size of output buffer.
 */
static void read_package_name(char *buf, size_t sz) {
    buf[0] = '\0';
    FILE *f = fopen("/proc/self/cmdline", "rb");
    if (!f) { snprintf(buf, sz, "unknown"); return; }
    size_t n = fread(buf, 1, sz - 1, f);
    fclose(f);
    if (!n) { snprintf(buf, sz, "unknown"); return; }
    buf[n] = '\0';
    /* cmdline may contain NULLs; stop at first NUL or colon. */
    size_t i;
    for (i = 0; i < n && buf[i]; ++i) {}
    buf[i] = '\0';
    char *colon = strchr(buf, ':');
    if (colon) *colon = '\0';
    if (!buf[0]) snprintf(buf, sz, "unknown");
    LOGI("Package name: %s", buf);
}

/* -------------------------------------------------------------------------
 * Obtain data directory via JNI (Context.getFilesDir())
 * ------------------------------------------------------------------------- */
/**
 * @brief Retrieve the app's internal files directory using JNI.
 *
 * This is the preferred output location because it does not require
 * external storage permissions (Android 10+).  It mimics:
 *
 *   ActivityThread.currentApplication().getFilesDir().getAbsolutePath()
 *
 * The call may block until the Application object is created (up to
 * 30 seconds).
 *
 * @param out_buf Buffer to receive the path.
 * @param out_sz  Size of out_buf.
 * @return 1 on success, 0 on failure.
 */
static int get_files_dir_jni(char *out_buf, size_t out_sz) {
    if (!g_jvm) { LOGW("get_files_dir_jni: g_jvm NULL"); return 0; }

    JNIEnv *env      = NULL;
    int     attached = 0;
    int     result   = 0;

    jint rc = (*g_jvm)->GetEnv(g_jvm, (void **)&env, JNI_VERSION_1_6);
    if (rc == JNI_EDETACHED) {
        if ((*g_jvm)->AttachCurrentThread(g_jvm, &env, NULL) != JNI_OK) {
            LOGW("get_files_dir_jni: AttachCurrentThread failed");
            return 0;
        }
        attached = 1;
    } else if (rc != JNI_OK) {
        LOGW("get_files_dir_jni: GetEnv failed %d", (int)rc);
        return 0;
    }

    /*
     * Build JNI call chain:
     *   ActivityThread.currentApplication()  -> Application
     *   .getFilesDir()                       -> java.io.File
     *   .getAbsolutePath()                   -> String
     */
    jclass   cls_at   = NULL;
    jmethodID mid_ca  = NULL;
    jobject  app      = NULL;
    jclass   cls_ctx  = NULL;
    jmethodID mid_gfd = NULL;
    jobject  file     = NULL;
    jclass   cls_file = NULL;
    jmethodID mid_gap = NULL;
    jstring  path_str = NULL;
    const char *chars = NULL;

#define CLR_EXC() do { if ((*env)->ExceptionCheck(env)) \
                           (*env)->ExceptionClear(env); } while(0)

    cls_at = (*env)->FindClass(env, "android/app/ActivityThread");
    if (!cls_at) { CLR_EXC(); goto jni_done; }

    mid_ca = (*env)->GetStaticMethodID(env, cls_at,
                 "currentApplication", "()Landroid/app/Application;");
    if (!mid_ca) { CLR_EXC(); goto jni_done; }

    /* Wait for Application object (it may not be available immediately) */
    {
        int retry;
        for (retry = 0; retry < 30; ++retry) {
            app = (*env)->CallStaticObjectMethod(env, cls_at, mid_ca);
            CLR_EXC();
            if (app) break;
            if (retry % 5 == 0)
                LOGI("Waiting for Application object (%d/30)...", retry);
            sleep(1);
        }
    }
    if (!app) { LOGW("currentApplication() returned null"); goto jni_done; }

    cls_ctx = (*env)->FindClass(env, "android/content/Context");
    if (!cls_ctx) { CLR_EXC(); goto jni_done; }

    mid_gfd = (*env)->GetMethodID(env, cls_ctx,
                  "getFilesDir", "()Ljava/io/File;");
    if (!mid_gfd) { CLR_EXC(); goto jni_done; }

    file = (*env)->CallObjectMethod(env, app, mid_gfd);
    CLR_EXC();
    if (!file) { LOGW("getFilesDir() returned null"); goto jni_done; }

    cls_file = (*env)->FindClass(env, "java/io/File");
    if (!cls_file) { CLR_EXC(); goto jni_done; }

    mid_gap = (*env)->GetMethodID(env, cls_file,
                  "getAbsolutePath", "()Ljava/lang/String;");
    if (!mid_gap) { CLR_EXC(); goto jni_done; }

    path_str = (jstring)(*env)->CallObjectMethod(env, file, mid_gap);
    CLR_EXC();
    if (!path_str) goto jni_done;

    chars = (*env)->GetStringUTFChars(env, path_str, NULL);
    if (chars && chars[0]) {
        strncpy(out_buf, chars, out_sz - 1);
        out_buf[out_sz - 1] = '\0';
        result = 1;
        LOGI("getFilesDir() = %s", out_buf);
    }
    if (chars) (*env)->ReleaseStringUTFChars(env, path_str, chars);

jni_done:
    /* Clean up local references */
    if (path_str) (*env)->DeleteLocalRef(env, path_str);
    if (cls_file) (*env)->DeleteLocalRef(env, cls_file);
    if (file)     (*env)->DeleteLocalRef(env, file);
    if (cls_ctx)  (*env)->DeleteLocalRef(env, cls_ctx);
    if (app)      (*env)->DeleteLocalRef(env, app);
    if (cls_at)   (*env)->DeleteLocalRef(env, cls_at);

    if (attached) (*g_jvm)->DetachCurrentThread(g_jvm);
    return result;

#undef CLR_EXC
}

/* -------------------------------------------------------------------------
 * Locate libil2cpp.so in the process memory map
 * ------------------------------------------------------------------------- */
/**
 * @brief Parse /proc/self/maps to find the base address and path of
 *        libil2cpp.so.
 *
 * The function searches for a mapping where the file offset is 0
 * (the first loadable segment) and the path ends with "libil2cpp.so".
 *
 * @param out_path  Buffer for the absolute path (may be empty).
 * @param path_sz   Size of out_path.
 * @param out_base  Receives the mapped base address.
 * @return 1 if found, 0 otherwise.
 */
static int find_il2cpp_in_maps(char *out_path, size_t path_sz,
                                uintptr_t *out_base) {
    *out_base   = 0;
    out_path[0] = '\0';

    FILE *maps = fopen("/proc/self/maps", "r");
    if (!maps) return 0;

    char line[1024];
    int  found = 0;

    while (fgets(line, sizeof(line), maps)) {
        if (!strstr(line, "libil2cpp.so")) continue;

        unsigned long addr_s = 0, addr_e = 0, offset = 0, inode = 0;
        char          perms[8]       = {0};
        char          dev[16]        = {0};
        char          path[PATH_MAX] = {0};

        int r = sscanf(line, "%lx-%lx %7s %lx %15s %lu %4095s",
                       &addr_s, &addr_e, perms, &offset, dev, &inode, path);
        if (r < 7 || !path[0] || path[0] == '[') continue;

        const char *fn = strrchr(path, '/');
        fn = fn ? fn + 1 : path;
        if (strcmp(fn, "libil2cpp.so") != 0) continue;

        /* The first loadable segment has file offset 0 */
        if (offset == 0) {
            *out_base = (uintptr_t)addr_s;
            strncpy(out_path, path, path_sz - 1);
            out_path[path_sz - 1] = '\0';
            found = 1;
            LOGI("libil2cpp.so: base=0x%lx path=%s",
                 (unsigned long)addr_s, out_path);
            break;
        }
    }
    fclose(maps);
    return found;
}

 /* -------------------------------------------------------------------------
 * Background dump thread
 * ------------------------------------------------------------------------- */
/**
 * @brief Main dump thread routine.
 *
 * Steps (all performed under crash‑handler protection):
 *   1. Install SIGSEGV/SIGBUS handler and enter safe region.
 *   2. Wait for libil2cpp.so to appear in memory (up to 60 s).
 *   3. Identify the app package.
 *   4. Determine an output directory:
 *        a. JNI‑acquired files dir (preferred, no permissions needed).
 *        b. /data/data/<pkg>/files/il2cpp_dump (fallback).
 *        c. /sdcard/il2cpp_dump (last resort).
 *   5. dlopen libil2cpp.so / RTLD_DEFAULT and resolve the IL2CPP API.
 *   6. Wait for domain, assemblies, and attach a thread.
 *   7. Invoke the dump (il2cpp_do_dump).
 *   8. Detach IL2CPP thread, uninstall crash handler, and exit.
 *
 * Any crash during steps 2‑7 causes a graceful abort
 * (log message, cleanup, thread exits).
 *
 * @param arg Unused.
 * @return Always NULL.
 */
static void *dump_thread(void *arg) {
    (void)arg;
#ifdef SYS_gettid
    LOGI("dump_thread tid=%ld", (long)syscall(SYS_gettid));
#endif

    /* Install crash handler and enter safe region. */
    install_crash_handler();
    g_in_dump = 1;
    int crash_sig = sigsetjmp(g_crash_jmp, 1);
    if (crash_sig != 0) {
        /* Crash occurred during dump; cleanly abort. */
        LOGE("dump_thread caught signal %d during setup/discovery; "
             "aborting safely.", crash_sig);
        g_in_dump = 0;
        uninstall_crash_handler();
        return NULL;
    }
    
    char      il2cpp_path[PATH_MAX] = {0};
    uintptr_t il2cpp_base = 0;
    int       r;

    /* Wait until libil2cpp.so is mapped.  Some games load it lazily. */
    {
        int found = 0;
        for (r = 0; r < 60 && !found; ++r) {
            found = find_il2cpp_in_maps(il2cpp_path, sizeof(il2cpp_path),
                                        &il2cpp_base);
            if (!found) {
                if (r % 10 == 0)
                    LOGI("Waiting for libil2cpp.so... (%d/60)", r);
                sleep(1);
            }
        }
        if (!found) {
            LOGE("libil2cpp.so not found after 60 s. Not an il2cpp game?");
            return NULL;
        }
    }

    /* Identify the app package (for output path construction). */
    char pkg[256] = {0};
    read_package_name(pkg, sizeof(pkg));

    char output_dir[PATH_MAX] = {0};

    /* Strategy 1: JNI‑based getFilesDir. */
    {
        char files_dir[PATH_MAX] = {0};
        if (get_files_dir_jni(files_dir, sizeof(files_dir))) {
            snprintf(output_dir, sizeof(output_dir),
                     "%s/il2cpp_dump", files_dir);
            mkdir(output_dir, 0755);   /* best effort */
            LOGI("Output dir (JNI): %s", output_dir);
        }
    }

    /* Strategy 2: Construct directory from package name. */
    if (!output_dir[0] && pkg[0] && strcmp(pkg, "unknown") != 0) {
        snprintf(output_dir, sizeof(output_dir),
                 "/data/data/%s/files/il2cpp_dump", pkg);
        mkdir_p(output_dir);
        LOGI("Output dir (cmdline): %s", output_dir);
    }

    /* Strategy 3: Fallback to /sdcard. */
    if (!output_dir[0]) {
        snprintf(output_dir, sizeof(output_dir), "/sdcard/il2cpp_dump");
        mkdir_p(output_dir);
        LOGW("Output dir (sdcard fallback): %s", output_dir);
    }

    /* Obtain a handle to resolve IL2CPP API functions.
     * Try: already loaded libil2cpp.so, then explicit dlopen, then global. */
    void *handle = dlopen(il2cpp_path, RTLD_NOLOAD | RTLD_NOW);
    if (!handle) handle = dlopen("libil2cpp.so", RTLD_NOLOAD | RTLD_NOW);
    if (!handle) {
        void *probe = dlsym(RTLD_DEFAULT, "il2cpp_domain_get");
        if (probe) handle = RTLD_DEFAULT;
    }
    LOGI("dlopen handle: %p  (%s)",
         handle, handle ? "dlsym path" : "ELF resolver path");

    /* Initialise function pointer table and compute base address. */
    if (!il2cpp_api_init_ex(handle, il2cpp_base)) {
        LOGE("il2cpp_api_init_ex failed. Aborting.");
        return NULL;
    }

    /* Wait for IL2CPP domain to become available (runtime may still be
       initialising). */
    LOGI("Waiting for il2cpp domain...");
    for (r = 0; r < 60; ++r) {
        if (il2cpp_domain_get && il2cpp_domain_get()) break;
        sleep(1);
    }
    if (!il2cpp_domain_get || !il2cpp_domain_get()) {
        LOGW("Domain not ready after 60 s; attempting dump anyway.");
    } else {
        LOGI("Domain ready.");
    }
    sleep(1); /* extra settling time */

    /* Attach the current thread to the IL2CPP domain (necessary for some
       API calls that require a managed thread context). */
    Il2CppThread *il2cpp_thread = NULL;
    if (il2cpp_domain_get && il2cpp_thread_attach) {
        Il2CppDomain *dom = il2cpp_domain_get();
        if (dom) {
            il2cpp_thread = il2cpp_thread_attach(dom);
            if (il2cpp_thread) LOGI("Thread attached to il2cpp domain.");
        }
    }

    /* Wait for at least one assembly to be loaded (indicates the runtime
       has finished loading the main application code). */
    LOGI("Waiting for assemblies...");
    {
        size_t asm_count = 0;
        for (r = 0; r < 30; ++r) {
            if (il2cpp_domain_get && il2cpp_domain_get_assemblies) {
                Il2CppDomain *dom = il2cpp_domain_get();
                if (dom) {
                    const Il2CppAssembly **list =
                        il2cpp_domain_get_assemblies(dom, &asm_count);
                    if (list && asm_count > 0) {
                        LOGI("Assemblies ready: %zu loaded.", asm_count);
                        break;
                    }
                }
            }
            if (r % 5 == 0)
                LOGI("Assemblies not ready yet (%d/30)...", r);
            sleep(1);
        }
        if (!asm_count)
            LOGW("Assembly count still 0 after 30 s; proceeding anyway.");
    }

    /* Ensure output directory exists. */
    mkdir(output_dir, 0755);
    char output_file[PATH_MAX];
    snprintf(output_file, sizeof(output_file), "%s/dump.cs", output_dir);

    /* Normal execution path. */
    int ok = il2cpp_do_dump(output_file);
    if (ok) { LOGI("SUCCESS: %s", output_file); }
    else    { LOGE("FAILED:  %s", output_file); }

    /* Detach from IL2CPP domain if we attached earlier. */
    if (il2cpp_thread && il2cpp_thread_detach) {
        il2cpp_thread_detach(il2cpp_thread);
    }

    g_in_dump = 0;
    uninstall_crash_handler();
    return NULL;
}

/* -------------------------------------------------------------------------
 * Thread spawn helper
 * ------------------------------------------------------------------------- */
/**
 * @brief Create a detached thread that will execute the dump.
 *
 * The detached attribute means we never need to join it; the system
 * reclaims its resources automatically when it exits.
 */
static void spawn_dump_thread(void) {
    pthread_t      tid;
    pthread_attr_t attr;

    pthread_attr_init(&attr);
    pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED);

    int rc = pthread_create(&tid, &attr, dump_thread, NULL);
    if (rc) { LOGE("pthread_create failed: %d (%s)", rc, strerror(rc)); }
    else    { LOGI("Dump thread spawned."); }

    pthread_attr_destroy(&attr);
}

/* -------------------------------------------------------------------------
 * Library constructor / JNI entry points
 * ------------------------------------------------------------------------- */
/**
 * @brief Constructor executed when the shared library is loaded.
 *
 * Immediately spawns the background dump thread.  The thread will wait
 * for the IL2CPP runtime to become ready before performing the dump.
 */
__attribute__((constructor))
static void il2cpp_dumper_constructor(void) {
    LOGI("il2cpp_dumper: constructor entry");
    spawn_dump_thread();
}

/**
 * @brief Standard JNI_OnLoad entry point.
 *
 * Saves the JavaVM pointer for later JNI operations (e.g. getFilesDir)
 * and returns the supported JNI version.
 *
 * @param vm        JavaVM pointer.
 * @param reserved  Unused.
 * @return JNI_VERSION_1_6.
 */
JNIEXPORT jint JNICALL JNI_OnLoad(JavaVM *vm, void *reserved) {
    (void)reserved;
    g_jvm = vm;
    LOGI("JNI_OnLoad: JavaVM saved.");
    return JNI_VERSION_1_6;
}

/**
 * @brief JNI‑exported function `nativeStart` for manual triggering.
 *
 * Can be called from Java/Kotlin code:
 *   `com.il2cppapp.Il2CppDumper.nativeStart(String outDir)`
 *
 * Currently the `outDir` parameter is unused; the thread uses the
 * auto‑discovery logic for the output path.
 *
 * @param env      JNI environment.
 * @param cls      Calling class.
 * @param out_dir  (unused) Proposed output directory.
 */
JNIEXPORT void JNICALL JNI_EXPORT(JAVA_PKG_NATIVE, nativeStart)(
        JNIEnv *env, jclass cls, jstring out_dir) {
    (void)env; (void)cls; (void)out_dir;
    LOGI("nativeStart() -> spawn_dump_thread");
    spawn_dump_thread();
}