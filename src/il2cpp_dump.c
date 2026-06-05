/**
 * @file il2cpp_dump_new.c
 * @brief IL2CPP type enumeration and C#‑like dump routines (file descriptor version).
 *
 * This module contains the core logic for walking IL2CPP metadata and
 * writing a human‑readable, C#‑like representation of all managed types
 * to a file.  It supports three strategies, tried in order:
 *
 *   1. **image_get_class** – iterate assemblies → images → classes via
 *      `il2cpp_image_get_class`.  This is the fastest path when
 *      available.
 *   2. **class_for_each** – use `il2cpp_class_for_each` callback (available
 *      in newer IL2CPP builds).
 *   3. **reflection** – load each assembly via `System.Reflection.Assembly`,
 *      call `GetTypes()`, and dump the returned classes.  This is the
 *      slowest but most compatible fallback.
 *
 * @section output Output format
 * The resulting `dump.cs` file is NOT valid C#; it is a pseudo‑source
 * listing aimed at reverse engineers.  Each class is annotated with:
 *   - Assembly name (`// Dll: Assembly‑CSharp`).
 *   - Namespace.
 *   - Attribute flags (visibility, abstract/sealed, Serializable, etc.).
 *   - Fields with offset comment.
 *   - Properties with get/set accessors.
 *   - Methods with RVA/VA and parameter in/out/ref annotations.
 *
 * @note This version uses low‑level file descriptors and internal
 *       buffering instead of `stdio.h` functions.  `write()` replaces `fprintf()` because `fprintf()` uses
 *       `flockfile()` mutexes. A crash‑handling `siglongjmp()` while
 *       that mutex is held leads to deadlock and `SIGABRT` on bionic.
 *       `write()` is async‑signal‑safe and avoids this issue.
 */

#include "il2cpp_dump.h"
#include "il2cpp_api.h"
#include "il2cpp_tabledefs.h"
#include "log.h"

#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>


#define SBUF 4096

/* -------------------------------------------------------------------------
 * Internal buffering helpers (writev‑like for small buffers)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write a fixed‑size buffer to a file descriptor, retrying on short writes.
 *
 * @param fd   Output file descriptor.
 * @param buf  Data to write.
 * @param len  Number of bytes to write.
 */
static void safe_flush(int fd, const char *buf, size_t len) {
    if (fd < 0 || !len) return;
    size_t done = 0;
    while (done < len) {
        ssize_t r = write(fd, buf + done, len - done);
        if (r <= 0) break;
        done += (size_t)r;
    }
}

/**
 * @brief Write a NUL‑terminated string to a file descriptor.
 *
 * @param fd Output file descriptor.
 * @param s  String to write (may be NULL).
 */
static void safe_puts(int fd, const char *s) {
    if (fd >= 0 && s) safe_flush(fd, s, strlen(s));
}

/** Copy raw bytes `src` of length `n` into buffer `b` at position `p`, advancing `p`. */
#define B_RAW(b,p,s,n) do { size_t _n=(n); \
    if ((p)+_n<SBUF){memcpy((b)+(p),(s),_n);(p)+=_n;} } while(0)

/** Copy NUL‑terminated string `s` into buffer. */
#define B_STR(b,p,s) do { const char *_s=(s); \
    if (_s) B_RAW(b,p,_s,strlen(_s)); } while(0)

/** Write a single character `c` into buffer. */
#define B_CHR(b,p,c) do { if ((p)+1<SBUF)(b)[(p)++]=(c); } while(0)

/** Flush buffer `b` of size `p` to file descriptor `fd` and reset `p` to 0. */
#define B_FLUSH(fd,b,p) do { safe_flush((fd),(b),(p)); (p)=0; } while(0)

/* -------------------------------------------------------------------------
 * Numeric formatting helpers
 * ------------------------------------------------------------------------- */

/**
 * @brief Append an unsigned 64‑bit decimal number to the buffer.
 *
 * @param b   Buffer.
 * @param p   Current position (in/out).
 * @param v   Value to format.
 */
static void b_u64(char *b, size_t *p, unsigned long long v) {
    char t[24]; int n = snprintf(t, sizeof(t), "%llu", v);
    if (n > 0) B_RAW(b, *p, t, (size_t)n);
}

/**
 * @brief Append a hexadecimal number (`0x…`) to the buffer.
 *
 * @param b   Buffer.
 * @param p   Current position (in/out).
 * @param v   Value to format.
 */
static void b_hex(char *b, size_t *p, unsigned long v) {
    char t[24]; int n = snprintf(t, sizeof(t), "0x%lx", v);
    if (n > 0) B_RAW(b, *p, t, (size_t)n);
}

/**
 * @brief Append a `size_t` as hexadecimal (`0x…`) to the buffer.
 *
 * @param b   Buffer.
 * @param p   Current position (in/out).
 * @param v   Value to format.
 */
static void b_szx(char *b, size_t *p, size_t v) {
    char t[24]; int n = snprintf(t, sizeof(t), "0x%zx", v);
    if (n > 0) B_RAW(b, *p, t, (size_t)n);
}

/* -------------------------------------------------------------------------
 * Class name and type helpers (identical to original)
 * ------------------------------------------------------------------------- */

/**
 * @brief Safely obtain a class name.
 *
 * Returns `<null_class>` if the class pointer is NULL,
 * `<no_api>` if the name API is missing, or `<unnamed>` if the name itself
 * is NULL.
 *
 * @param klass IL2CPP class pointer.
 * @return Never‑NULL string.
 */
static const char *safe_class_name(Il2CppClass *klass) {
    if (!klass) return "<null_class>";
    if (!il2cpp_class_get_name) return "<no_api>";
    const char *n = il2cpp_class_get_name(klass);
    return n ? n : "<unnamed>";
}

/**
 * @brief Determine whether a type is passed by reference (`ref`).
 *
 * Falls back to reading the `byref` field directly if the API function
 * is not available.
 *
 * @param type IL2CPP type descriptor.
 * @return true if the type is a by‑reference type.
 */
static bool type_is_byref(const Il2CppType *type) {
    if (!type) return false;
    if (il2cpp_type_is_byref) return il2cpp_type_is_byref(type);
    return (bool)type->byref;
}

/* -------------------------------------------------------------------------
 * Attribute printing helpers (write to fd)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write C# access and method modifiers to the output file descriptor.
 *
 * Interprets the IL method flags (visibility, static, abstract, virtual,
 * override, sealed, extern) and prints the corresponding C# keywords.
 *
 * @param fd    Output file descriptor.
 * @param flags Raw method flags from IL2CPP metadata.
 */
static void write_method_modifier(int fd, uint32_t flags) {
    switch (flags & METHOD_ATTRIBUTE_MEMBER_ACCESS_MASK) {
    case METHOD_ATTRIBUTE_PRIVATE:        safe_puts(fd, "private ");            break;
    case METHOD_ATTRIBUTE_PUBLIC:         safe_puts(fd, "public ");             break;
    case METHOD_ATTRIBUTE_FAMILY:         safe_puts(fd, "protected ");          break;
    case METHOD_ATTRIBUTE_ASSEM:
    case METHOD_ATTRIBUTE_FAM_AND_ASSEM:  safe_puts(fd, "internal ");           break;
    case METHOD_ATTRIBUTE_FAM_OR_ASSEM:   safe_puts(fd, "protected internal "); break;
    default: break;
    }
    if (flags & METHOD_ATTRIBUTE_STATIC) safe_puts(fd, "static ");
    if (flags & METHOD_ATTRIBUTE_ABSTRACT) {
        safe_puts(fd, "abstract ");
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT)
            safe_puts(fd, "override ");
    } else if (flags & METHOD_ATTRIBUTE_FINAL) {
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_REUSE_SLOT)
            safe_puts(fd, "sealed override ");
    } else if (flags & METHOD_ATTRIBUTE_VIRTUAL) {
        if ((flags & METHOD_ATTRIBUTE_VTABLE_LAYOUT_MASK) == METHOD_ATTRIBUTE_NEW_SLOT)
            safe_puts(fd, "virtual ");
        else
            safe_puts(fd, "override ");
    }
    if (flags & METHOD_ATTRIBUTE_PINVOKE_IMPL) safe_puts(fd, "extern ");
}

/* -------------------------------------------------------------------------
 * Field dumper (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write field declarations to the output file descriptor.
 *
 * Also prints the field type, name, memory offset, and for literal enum
 * fields, the constant value.
 *
 * @param fd    Output file descriptor.
 * @param klass The enclosing class (used to detect enums).
 */
static void dump_fields(int fd, Il2CppClass *klass) {
    bool is_enum = il2cpp_class_is_enum ? il2cpp_class_is_enum(klass) : false;
    void *iter = NULL;
    FieldInfo *field;

    safe_puts(fd, "\n\t// Fields\n");

    while ((field = il2cpp_class_get_fields(klass, &iter)) != NULL) {
        int attrs  = il2cpp_field_get_flags(field);
        int access = attrs & FIELD_ATTRIBUTE_FIELD_ACCESS_MASK;

        char buf[SBUF]; size_t pos = 0;
        B_STR(buf, pos, "\t");
        switch (access) {
        case FIELD_ATTRIBUTE_PRIVATE:        B_STR(buf,pos,"private ");            break;
        case FIELD_ATTRIBUTE_PUBLIC:         B_STR(buf,pos,"public ");             break;
        case FIELD_ATTRIBUTE_FAMILY:         B_STR(buf,pos,"protected ");          break;
        case FIELD_ATTRIBUTE_ASSEMBLY:
        case FIELD_ATTRIBUTE_FAM_AND_ASSEM:  B_STR(buf,pos,"internal ");           break;
        case FIELD_ATTRIBUTE_FAM_OR_ASSEM:   B_STR(buf,pos,"protected internal "); break;
        default: break;
        }
        if (attrs & FIELD_ATTRIBUTE_LITERAL) {
            B_STR(buf, pos, "const ");
        } else {
            if (attrs & FIELD_ATTRIBUTE_STATIC)    B_STR(buf, pos, "static ");
            if (attrs & FIELD_ATTRIBUTE_INIT_ONLY) B_STR(buf, pos, "readonly ");
        }

        const Il2CppType *ftype  = il2cpp_field_get_type(field);
        Il2CppClass      *fclass = ftype ? il2cpp_class_from_type(ftype) : NULL;
        const char       *fname  = il2cpp_field_get_name(field);

        B_STR(buf, pos, safe_class_name(fclass));
        B_CHR(buf, pos, ' ');
        B_STR(buf, pos, fname ? fname : "<unnamed>");

        if ((attrs & FIELD_ATTRIBUTE_LITERAL) && is_enum
                && il2cpp_field_static_get_value) {
            uint64_t val = 0;
            il2cpp_field_static_get_value(field, &val);
            B_STR(buf, pos, " = ");
            b_u64(buf, &pos, (unsigned long long)val);
        }

        size_t offset = il2cpp_field_get_offset(field);
        B_STR(buf, pos, "; // ");
        b_szx(buf, &pos, offset);
        B_CHR(buf, pos, '\n');
        B_FLUSH(fd, buf, pos);
    }
}

/* -------------------------------------------------------------------------
 * Property dumper (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write property declarations.
 *
 * Determines the property type from the getter's return type or the
 * setter's first parameter, then prints the property with `get;` / `set;`
 * accessor placeholders.
 *
 * @param fd    Output file descriptor.
 * @param klass Enclosing class.
 */
static void dump_properties(int fd, Il2CppClass *klass) {
    void *iter = NULL;
    const PropertyInfo *prop;

    safe_puts(fd, "\n\t// Properties\n");

    while ((prop = il2cpp_class_get_properties(klass, &iter)) != NULL) {
        PropertyInfo     *p     = (PropertyInfo *)prop;
        const MethodInfo *get   = il2cpp_property_get_get_method(p);
        const MethodInfo *set   = il2cpp_property_get_set_method(p);
        const char       *pname = il2cpp_property_get_name(p);

        Il2CppClass *prop_class = NULL;
        uint32_t     iflags     = 0;
        uint32_t     flags      = 0;

        if (get) {
            flags = il2cpp_method_get_flags(get, &iflags);
            const Il2CppType *rtype = il2cpp_method_get_return_type(get);
            if (rtype) prop_class = il2cpp_class_from_type(rtype);
        } else if (set) {
            flags = il2cpp_method_get_flags(set, &iflags);
            if (il2cpp_method_get_param_count(set) > 0) {
                const Il2CppType *ptype = il2cpp_method_get_param(set, 0);
                if (ptype) prop_class = il2cpp_class_from_type(ptype);
            }
        }

        if (!prop_class) {
            if (pname) {
                char buf[256]; size_t pos = 0;
                B_STR(buf,pos,"\t// unknown property ");
                B_STR(buf,pos,pname); B_CHR(buf,pos,'\n');
                B_FLUSH(fd,buf,pos);
            }
            continue;
        }

        safe_puts(fd, "\t");
        write_method_modifier(fd, flags);

        char buf[SBUF]; size_t pos = 0;
        B_STR(buf,pos,safe_class_name(prop_class)); B_CHR(buf,pos,' ');
        B_STR(buf,pos,pname ? pname : "<unnamed>"); B_STR(buf,pos," { ");
        if (get) B_STR(buf,pos,"get; ");
        if (set) B_STR(buf,pos,"set; ");
        B_STR(buf,pos,"}\n");
        B_FLUSH(fd,buf,pos);
    }
}

/* -------------------------------------------------------------------------
 * Method dumper (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write method declarations.
 *
 * Includes the RVA (relative virtual address) and VA (absolute) as
 * a comment, then prints the method signature: modifiers, return type,
 * name, and parameter list (`ref`, `out`, `in`, `[In]`, `[Out]`).
 *
 * @param fd    Output file descriptor.
 * @param klass Enclosing class.
 * @param base  Base address of libil2cpp.so (for RVA calculation).
 */
static void dump_methods(int fd, Il2CppClass *klass, uintptr_t base) {
    void *iter = NULL;
    const MethodInfo *method;

    safe_puts(fd, "\n\t// Methods\n");

    while ((method = il2cpp_class_get_methods(klass, &iter)) != NULL) {
        // Address comment
        {
            char buf[128]; size_t pos = 0;
            if (method->methodPointer) {
                uintptr_t va  = (uintptr_t)method->methodPointer;
                uintptr_t rva = (base && va > base) ? (va - base) : va;
                B_STR(buf,pos,"\t// RVA: "); b_hex(buf,&pos,(unsigned long)rva);
                B_STR(buf,pos," VA: ");      b_hex(buf,&pos,(unsigned long)va);
            } else {
                B_STR(buf,pos,"\t// RVA: 0x0 VA: 0x0");
            }
            B_CHR(buf,pos,'\n'); B_FLUSH(fd,buf,pos);
        }

        safe_puts(fd, "\t");

        uint32_t iflags = 0;
        uint32_t flags  = il2cpp_method_get_flags(method, &iflags);
        write_method_modifier(fd, flags);

        const Il2CppType *rtype  = il2cpp_method_get_return_type(method);
        Il2CppClass      *rclass = rtype ? il2cpp_class_from_type(rtype) : NULL;

        {
            char buf[SBUF]; size_t pos = 0;
            if (rtype && type_is_byref(rtype)) B_STR(buf,pos,"ref ");
            B_STR(buf,pos,safe_class_name(rclass)); B_CHR(buf,pos,' ');
            const char *mname = il2cpp_method_get_name(method);
            B_STR(buf,pos,mname ? mname : "<unnamed>"); B_CHR(buf,pos,'(');
            B_FLUSH(fd,buf,pos);

            uint32_t param_count = il2cpp_method_get_param_count(method);
            uint32_t i;
            for (i = 0; i < param_count; ++i) {
                const Il2CppType *param  = il2cpp_method_get_param(method, i);
                Il2CppClass      *pclass = param ? il2cpp_class_from_type(param) : NULL;
                char pbuf[256]; size_t ppos = 0;

                if (param && type_is_byref(param)) {
                    uint32_t pa  = param->attrs;
                    bool is_out  = (pa & PARAM_ATTRIBUTE_OUT) && !(pa & PARAM_ATTRIBUTE_IN);
                    bool is_in   = (pa & PARAM_ATTRIBUTE_IN)  && !(pa & PARAM_ATTRIBUTE_OUT);
                    if (is_out)      B_STR(pbuf,ppos,"out ");
                    else if (is_in)  B_STR(pbuf,ppos,"in ");
                    else             B_STR(pbuf,ppos,"ref ");
                } else if (param) {
                    uint32_t pa = param->attrs;
                    if (pa & PARAM_ATTRIBUTE_IN)  B_STR(pbuf,ppos,"[In] ");
                    if (pa & PARAM_ATTRIBUTE_OUT) B_STR(pbuf,ppos,"[Out] ");
                }

                const char *pname = il2cpp_method_get_param_name
                                    ? il2cpp_method_get_param_name(method, i)
                                    : NULL;
                B_STR(pbuf,ppos,safe_class_name(pclass)); B_CHR(pbuf,ppos,' ');
                B_STR(pbuf,ppos,pname ? pname : "param");
                if (i + 1 < param_count) B_STR(pbuf,ppos,", ");
                B_FLUSH(fd,pbuf,ppos);
            }
        }
        safe_puts(fd, ") { }\n");
    }
}

/* -------------------------------------------------------------------------
 * Single class dump (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Write the C#‑like declaration of a single IL2CPP class.
 *
 * The output includes:
 *   - Namespace comment.
 *   - Attributes (visibility, Serializable, abstract/sealed/static, etc.).
 *   - Kind (class, struct, enum, interface).
 *   - Base type and implemented interfaces.
 *   - Fields, properties, and methods.
 *
 * @param fd    Output file descriptor.
 * @param klass IL2CPP class to dump.
 * @param base  libil2cpp.so base address for RVA calculation.
 */
static void dump_single_class(int fd, Il2CppClass *klass, uintptr_t base) {
    if (!klass || !il2cpp_class_get_type) return;
    const Il2CppType *type = il2cpp_class_get_type(klass);
    if (!type) return;

    const char *ns = il2cpp_class_get_namespace ? il2cpp_class_get_namespace(klass) : "";
    {
        char buf[256]; size_t pos = 0;
        B_STR(buf,pos,"\n// Namespace: "); B_STR(buf,pos,ns?ns:""); B_CHR(buf,pos,'\n');
        B_FLUSH(fd,buf,pos);
    }

    int  flags        = il2cpp_class_get_flags   ? il2cpp_class_get_flags(klass)      : 0;
    bool is_valuetype = il2cpp_class_is_valuetype ? il2cpp_class_is_valuetype(klass)   : false;
    bool is_enum      = il2cpp_class_is_enum      ? il2cpp_class_is_enum(klass)        : false;
    bool is_interface = (flags & TYPE_ATTRIBUTE_INTERFACE) != 0;
    bool is_abstract  = (flags & TYPE_ATTRIBUTE_ABSTRACT)  != 0;
    bool is_sealed    = (flags & TYPE_ATTRIBUTE_SEALED)    != 0;

    if (flags & TYPE_ATTRIBUTE_SERIALIZABLE) safe_puts(fd, "[Serializable]\n");

    char buf[SBUF]; size_t pos = 0;
    switch (flags & TYPE_ATTRIBUTE_VISIBILITY_MASK) {
    case TYPE_ATTRIBUTE_PUBLIC:
    case TYPE_ATTRIBUTE_NESTED_PUBLIC:        B_STR(buf,pos,"public ");             break;
    case TYPE_ATTRIBUTE_NOT_PUBLIC:
    case TYPE_ATTRIBUTE_NESTED_FAM_AND_ASSEM:
    case TYPE_ATTRIBUTE_NESTED_ASSEMBLY:      B_STR(buf,pos,"internal ");           break;
    case TYPE_ATTRIBUTE_NESTED_PRIVATE:       B_STR(buf,pos,"private ");            break;
    case TYPE_ATTRIBUTE_NESTED_FAMILY:        B_STR(buf,pos,"protected ");          break;
    case TYPE_ATTRIBUTE_NESTED_FAM_OR_ASSEM:  B_STR(buf,pos,"protected internal "); break;
    default: break;
    }
    if      (is_abstract && is_sealed)              B_STR(buf,pos,"static ");
    else if (!is_interface && is_abstract)           B_STR(buf,pos,"abstract ");
    else if (!is_valuetype && !is_enum && is_sealed) B_STR(buf,pos,"sealed ");

    if      (is_interface) B_STR(buf,pos,"interface ");
    else if (is_enum)      B_STR(buf,pos,"enum ");
    else if (is_valuetype) B_STR(buf,pos,"struct ");
    else                   B_STR(buf,pos,"class ");
    B_STR(buf,pos,safe_class_name(klass));

    // Base class and interfaces
    {
        char sep[4] = " : ";
        if (!is_valuetype && !is_enum && il2cpp_class_get_parent && il2cpp_class_get_type) {
            Il2CppClass *parent = il2cpp_class_get_parent(klass);
            if (parent) {
                const Il2CppType *pt = il2cpp_class_get_type(parent);
                if (pt && pt->type != IL2CPP_TYPE_OBJECT) {
                    B_STR(buf,pos,sep); B_STR(buf,pos,safe_class_name(parent));
                    memcpy(sep,", ",3);
                }
            }
        }
        if (il2cpp_class_get_interfaces) {
            void *iter = NULL; Il2CppClass *itf;
            while ((itf = il2cpp_class_get_interfaces(klass, &iter)) != NULL) {
                B_STR(buf,pos,sep); B_STR(buf,pos,safe_class_name(itf));
                memcpy(sep,", ",3);
            }
        }
    }
    B_STR(buf,pos,"\n{\n");
    B_FLUSH(fd,buf,pos);

    dump_fields(fd, klass);
    dump_properties(fd, klass);
    dump_methods(fd, klass, base);
    safe_puts(fd, "}\n");
}

/* -------------------------------------------------------------------------
 * Strategy 1: Dump via image_get_class (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Dump all classes by iterating assemblies → images → classes.
 *
 * Requires `il2cpp_image_get_class` and `il2cpp_image_get_class_count`.
 * Each class is annotated with the DLL (image) name.
 *
 * @param fd   Output file descriptor.
 * @param base libil2cpp.so base address.
 * @return 1 on success, 0 if the required APIs are missing.
 */
static int dump_by_image(int fd, uintptr_t base) {
    if (!il2cpp_image_get_class || !il2cpp_image_get_class_count) {
        LOGI("il2cpp_image_get_class not available; trying fallback");
        return 0;
    }

    Il2CppDomain        *domain    = il2cpp_domain_get();
    size_t               asm_count = 0;
    const Il2CppAssembly **assemblies = il2cpp_domain_get_assemblies(domain, &asm_count);

    if (!assemblies || asm_count == 0) {
        LOGE("No assemblies found in domain");
        return 0;
    }

    LOGI("Dumping %zu assemblies (strategy: image_get_class)", asm_count);

    // First pass: list assemblies for readability
    size_t i;
    for (i = 0; i < asm_count; ++i) {
        const Il2CppImage *img  = il2cpp_assembly_get_image(assemblies[i]);
        const char        *name = img ? il2cpp_image_get_name(img) : "?";
        char buf[256]; size_t pos = 0;
        B_STR(buf,pos,"// Image "); b_u64(buf,&pos,(unsigned long long)i);
        B_STR(buf,pos,": "); B_STR(buf,pos,name?name:"?"); B_CHR(buf,pos,'\n');
        B_FLUSH(fd,buf,pos);
    }

    // Second pass: dump classes grouped by assembly
    for (i = 0; i < asm_count; ++i) {
        const Il2CppImage *img = il2cpp_assembly_get_image(assemblies[i]);
        if (!img) continue;
        const char *img_name = il2cpp_image_get_name(img);
        size_t      cnt      = il2cpp_image_get_class_count(img);
        size_t j;
        for (j = 0; j < cnt; ++j) {
            const Il2CppClass *klass = il2cpp_image_get_class(img, j);
            if (!klass) continue;
            char buf[256]; size_t pos = 0;
            B_STR(buf,pos,"\n// Dll: "); B_STR(buf,pos,img_name?img_name:"?");
            B_FLUSH(fd,buf,pos);
            dump_single_class(fd, (Il2CppClass *)klass, base);
        }
    }
    return 1;
}

/* -------------------------------------------------------------------------
 * Strategy 2: Dump via il2cpp_class_for_each (fd version)
 * ------------------------------------------------------------------------- */

/**
 * @brief Callback context for `dump_by_for_each`.
 */
typedef struct {
    int fd;           /**< Output file descriptor. */
    uintptr_t base;   /**< libil2cpp.so base address. */
    size_t count;     /**< Number of classes written (accumulated). */
} ForEachCtx;

/**
 * @brief Callback invoked by `il2cpp_class_for_each`.
 *
 * Writes the class declaration with the DLL name obtained from
 * `il2cpp_class_get_image`.
 *
 * @param klass     Current class.
 * @param user_data Pointer to a ForEachCtx structure.
 */
static void for_each_callback(Il2CppClass *klass, void *user_data) {
    ForEachCtx *ctx = (ForEachCtx *)user_data;
    const char *dll = "?";
    if (il2cpp_class_get_image) {
        const Il2CppImage *img = il2cpp_class_get_image(klass);
        if (img && il2cpp_image_get_name) {
            const char *n = il2cpp_image_get_name((Il2CppImage*)img);
            if (n) dll = n;
        }
    }
    char buf[256]; size_t pos = 0;
    B_STR(buf,pos,"\n// Dll: "); B_STR(buf,pos,dll); B_FLUSH(ctx->fd,buf,pos);
    dump_single_class(ctx->fd, klass, ctx->base);
    ctx->count++;
}

/**
 * @brief Dump all classes using `il2cpp_class_for_each`.
 *
 * Requires the `il2cpp_class_for_each` function pointer.
 *
 * @param fd   Output file descriptor.
 * @param base libil2cpp.so base address.
 * @return 1 if at least one class was written, 0 otherwise.
 */
static int dump_by_for_each(int fd, uintptr_t base) {
    if (!il2cpp_class_for_each) return 0;
    LOGI("Dumping via il2cpp_class_for_each (strategy: for_each)");
    ForEachCtx ctx; ctx.fd = fd; ctx.base = base; ctx.count = 0;
    il2cpp_class_for_each(for_each_callback, &ctx);
    LOGI("il2cpp_class_for_each enumerated %zu classes", ctx.count);
    return (ctx.count > 0) ? 1 : 0;
}

/* -------------------------------------------------------------------------
 * Strategy 3: Reflection‑based dump (slow fallback, fd version)
 * ------------------------------------------------------------------------- */

/** Prototype for Assembly.Load(string) */
typedef void *(*AssemblyLoad_ftn)(void *, Il2CppString *, void *);
/** Prototype for Assembly.GetTypes() */
typedef Il2CppArray *(*AssemblyGetTypes_ftn)(void *, void *);

/**
 * @brief Dump all classes using .NET reflection APIs.
 *
 * This strategy requires `il2cpp_get_corlib` and
 * `il2cpp_class_from_system_type`.  It loads each assembly by name via
 * `Assembly.Load`, calls `GetTypes()`, and dumps each returned
 * `System.Type` by converting it back to an `Il2CppClass`.
 *
 * @param fd   Output file descriptor.
 * @param base libil2cpp.so base address.
 * @return 1 on success, 0 if necessary APIs are missing.
 */
static int dump_by_reflection(int fd, uintptr_t base) {
    if (!il2cpp_get_corlib || !il2cpp_class_from_name ||
        !il2cpp_class_get_method_from_name || !il2cpp_string_new ||
        !il2cpp_class_from_system_type) {
        LOGW("Reflection APIs unavailable; cannot fall back to GetTypes()");
        return 0;
    }

    const Il2CppImage *corlib    = il2cpp_get_corlib();
    Il2CppClass *asm_class = il2cpp_class_from_name(corlib,"System.Reflection","Assembly");
    if (!asm_class) { LOGE("Cannot find System.Reflection.Assembly"); return 0; }

    const MethodInfo *load_method  = il2cpp_class_get_method_from_name(asm_class,"Load",1);
    const MethodInfo *types_method = il2cpp_class_get_method_from_name(asm_class,"GetTypes",0);

    if (!load_method  || !load_method->methodPointer)  { LOGE("Assembly.Load not found");     return 0; }
    if (!types_method || !types_method->methodPointer) { LOGE("Assembly.GetTypes not found"); return 0; }

    AssemblyLoad_ftn     fn_load  = (AssemblyLoad_ftn)    load_method->methodPointer;
    AssemblyGetTypes_ftn fn_types = (AssemblyGetTypes_ftn)types_method->methodPointer;

    Il2CppDomain *domain = il2cpp_domain_get();
    size_t asm_count = 0;
    const Il2CppAssembly **assemblies = il2cpp_domain_get_assemblies(domain, &asm_count);
    if (!assemblies || asm_count == 0) {
        LOGE("No assemblies for reflection dump");
        return 0;
    }

    LOGI("Reflection dump: %zu assemblies", asm_count);

    size_t i;
    for (i = 0; i < asm_count; ++i) {
        const Il2CppImage *img = il2cpp_assembly_get_image(assemblies[i]);
        if (!img) continue;
        const char *img_name = il2cpp_image_get_name(img); if (!img_name) img_name="?";

        // Strip .dll extension to get the assembly name for Load()
        char asm_name[256];
        strncpy(asm_name,img_name,sizeof(asm_name)-1); asm_name[sizeof(asm_name)-1]='\0';
        char *dot = strrchr(asm_name,'.'); if (dot) *dot='\0';

        Il2CppString *asm_str  = il2cpp_string_new(asm_name);
        void         *refl_asm = fn_load(NULL,asm_str,NULL);
        if (!refl_asm) {
            LOGW("Assembly.Load failed for: %s",asm_name);
            continue;
        }
        Il2CppArray *types = fn_types(refl_asm,NULL);
        if (!types) continue;

        il2cpp_array_size_t j;
        for (j = 0; j < types->max_length; ++j) {
            Il2CppReflectionType *rt    = (Il2CppReflectionType *)types->vector[j];
            Il2CppClass          *klass = il2cpp_class_from_system_type(rt);
            if (!klass) continue;
            char buf[256]; size_t pos=0;
            B_STR(buf,pos,"\n// Dll: "); B_STR(buf,pos,img_name); B_FLUSH(fd,buf,pos);
            dump_single_class(fd,klass,base);
        }
    }
    return 1;
}

/* -------------------------------------------------------------------------
 * Public API: initialisation helper & main dump entry
 * ------------------------------------------------------------------------- */

/**
 * @brief Block until the IL2CPP domain is available.
 *
 * Polls `il2cpp_domain_get` every second for up to 60 seconds.
 * If the function pointer itself is NULL, we cannot perform the check
 * and simply wait for 3 seconds before returning success.
 *
 * @return 1 if the domain is ready, 0 on timeout.
 */
int il2cpp_wait_for_init(void) {
    LOGI("Waiting for il2cpp domain to become ready...");
    if (!il2cpp_domain_get) {
        LOGW("il2cpp_domain_get unavailable; skipping init check");
        sleep(3);
        return 1;
    }
    int timeout = 60;
    while (timeout-- > 0) {
        Il2CppDomain *d = il2cpp_domain_get();
        if (d) {
            LOGI("il2cpp domain ready (%p)", (void*)d);
            return 1;
        }
        sleep(1);
    }
    LOGE("Timed out waiting for il2cpp domain");
    return 0;
}

/**
 * @brief Perform the IL2CPP metadata dump (file descriptor version).
 *
 * Opens the output file (retrying up to 10 times if the directory
 * does not exist, and falling back to alternative paths on failure),
 * determines the base address of libil2cpp.so, and tries the three
 * dumping strategies in order.
 *
 * @param output_path Desired path for the dump file (e.g. /.../dump.cs).
 * @return 1 on success, 0 on failure.
 */
int il2cpp_do_dump(const char *output_path) {
    if (!output_path) { LOGE("output_path is NULL"); return 0; }

    // Retry-based file opening with directory creation (fd version)
    int  out_fd = -1;
    int  attempt;
    for (attempt = 1; attempt <= 10; ++attempt) {
        char dir[512]; strncpy(dir,output_path,sizeof(dir)-1); dir[sizeof(dir)-1]='\0';
        char *slash = strrchr(dir,'/');
        if (slash) {
            *slash = '\0';
            char tmp[512]; strncpy(tmp,dir,sizeof(tmp)-1); tmp[sizeof(tmp)-1]='\0';
            char *p; for (p=tmp+1;*p;++p){if(*p=='/'){*p='\0';mkdir(tmp,0755);*p='/';}} mkdir(tmp,0755);
        }
        out_fd = open(output_path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
        if (out_fd >= 0) {
            LOGI("Output file opened on attempt %d: %s", attempt, output_path);
            break;
        }
        LOGW("open attempt %d/10 failed: %s errno=%d (%s)",
             attempt, output_path, errno, strerror(errno));
        if (attempt < 10) sleep(1);
    }

    // Fallback paths when the primary path cannot be opened (fd version)
    if (out_fd < 0) {
        char pkg[256]={0};
        const char *p = strstr(output_path,"/data/data/");
        if (p) {
            p += strlen("/data/data/");
            const char *sl = strchr(p,'/');
            size_t ln = sl?(size_t)(sl-p):strlen(p);
            if (ln<sizeof(pkg)){memcpy(pkg,p,ln);pkg[ln]='\0';}
        }
        char fb0[512],fb1[512],fb2[512]; const char *fbs[3]; int nfb=0;
        if (pkg[0]) {
            snprintf(fb0,sizeof(fb0),"/sdcard/Android/data/%s/files/il2cpp_dump",pkg);
            snprintf(fb1,sizeof(fb1),"/storage/emulated/0/Android/data/%s/files/il2cpp_dump",pkg);
            fbs[nfb++]=fb0; fbs[nfb++]=fb1;
        }
        snprintf(fb2,sizeof(fb2),"/sdcard/il2cpp_dump"); fbs[nfb++]=fb2;
        int fi;
        for (fi=0; fi<nfb && out_fd<0; ++fi) {
            {
                char tmp[512]; strncpy(tmp,fbs[fi],sizeof(tmp)-1); tmp[sizeof(tmp)-1]='\0';
                char *q; for(q=tmp+1;*q;++q){if(*q=='/'){*q='\0';mkdir(tmp,0755);*q='/';}} mkdir(tmp,0755);
            }
            char fb_file[640]; snprintf(fb_file,sizeof(fb_file),"%s/dump.cs",fbs[fi]);
            out_fd = open(fb_file,O_WRONLY|O_CREAT|O_TRUNC,0644);
            if (out_fd>=0) LOGI("Using fallback output path: %s",fb_file);
            else LOGW("Fallback also failed: %s errno=%d (%s)",fb_file,errno,strerror(errno));
        }
    }

    if (out_fd < 0) {
        LOGE("All output paths failed. Dump aborted.");
        return 0;
    }

    uintptr_t base = il2cpp_get_base();
    LOGI("il2cpp base: 0x%lx", (unsigned long)base);

    int ok = 0;
    if (!ok) ok = dump_by_image(out_fd, base);
    if (!ok) ok = dump_by_for_each(out_fd, base);
    if (!ok) ok = dump_by_reflection(out_fd, base);

    if (!ok) {
        // Record which APIs were missing for post‑mortem debugging
        char buf[256]; size_t pos=0;
        B_STR(buf,pos,"// ERROR: No suitable enumeration strategy found.\n");
        B_STR(buf,pos,"// il2cpp_image_get_class: ");
        B_STR(buf,pos,il2cpp_image_get_class?"available\n":"missing\n");
        B_STR(buf,pos,"// il2cpp_class_for_each: ");
        B_STR(buf,pos,il2cpp_class_for_each?"available\n":"missing\n");
        B_FLUSH(out_fd,buf,pos);
        LOGE("All dump strategies failed");
    }

    close(out_fd);
    if (ok) LOGI("Dump complete -> %s", output_path);
    return ok;
}