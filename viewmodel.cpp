// Anodize view model changer - the one piece of this app that runs inside the game.
//
// Why it cannot be the memory engine: the gun in your hands is drawn by its own
// Camera, and making it smaller means raising that camera's field of view, i.e.
// calling Camera.set_fieldOfView on a managed object. An external dword writer
// cannot make a call, and the float itself is one of some thousands of 60.0f in
// a Unity process with nothing to tell them apart from outside. So this half is
// injected and speaks il2cpp.
//
//   libinj.so <pid of the game> /data/local/tmp/libviewmodel.so
//
// Two files, inside the game's own data directory:
//   anodize_vm.cfg   "<fov> [camIndex] [hook]" - reread every 2 s, 0 fov is off
//   anodize_vm.txt   the camera list and what got picked, rewritten every 2 s
//
// They used to live in /data/local/tmp and that never worked for one press. That
// directory is shell_data_file, and untrusted_app - which is what this code runs
// as, because it runs as the game - has no search on it, so every open() here
// failed with EACCES no matter what label the files themselves were given. The
// symptom was a report that stayed zero bytes and a slider that did nothing.
// RootEngine now prepares the report's owner/mode and copies the game's data
// label onto the skin files, including files left by earlier builds.
//
// The cfg being polled is what makes one injection enough: moving the slider
// rewrites the file, and nothing has to be injected again.
//
// Everything of consequence also goes to logcat under the tag ANODIZE. A file
// can be unreachable and a report can be read after the process is already gone;
// logd takes writes from any app domain and keeps them after the writer dies,
// which makes it the only channel that survives the thing being diagnosed.
//
// Every name used here is Unity's own - Camera, get_allCameras, set_fieldOfView,
// LateUpdate - so nothing below breaks when the game updates. The game's own
// member names are obfuscated to things like ADEAAACFHADDAFG; Unity's cannot be,
// because the engine itself binds to them. The one version-pinned thing is the
// RVA table in il2cpp.hpp, cut for Standoff 2 0.39.2: the game's libunity.so
// exports no il2cpp symbol, so the API has to be reached by offset.

#include <cstdint>
#include <cstdarg>
#include <cstdio>
#include <cstring>
#include <cstdlib>
#include <cerrno>
#include <ctime>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>
#include <dlfcn.h>
#include <link.h>
#include <sys/mman.h>
#include <sys/uio.h>
#include <android/log.h>

#include "il2cpp.hpp"
#include "payload_protocol.hpp"

#define UNITY_LIB "libunity.so"
#ifndef VM_DIR
#define VM_DIR    "/data/data/com.axlebolt.standoff2"
#endif
#define CFG_PATH  VM_DIR "/anodize_vm.cfg"
#define OUT_PATH  VM_DIR "/anodize_vm.txt"

// The channel that cannot be taken away. inj resolves this against the game's
// own liblog.so, so it needs no file, no label and no permission.
#define LG(...) __android_log_print(ANDROID_LOG_INFO, "ANODIZE", __VA_ARGS__)

// ------------------------------------------------------- no libc string functions
//
// These four exist because of one line in inj.cpp: it binds imports by name and
// takes st_value as the answer. On arm64 bionic, memcpy, memmove, memset, memchr,
// strlen, strcmp and strncmp are all STT_GNU_IFUNC - their st_value is the address
// of a *resolver*, a function whose job is to return the real implementation for
// this CPU. Bind one by name and every call gets the resolver: strcmp(a, b) runs
// the chooser and hands back a pointer, which is non-zero, which reads as
// "different". So find_method compared every name in the class against the one it
// wanted and never matched a single one - the payload resolved nothing, hooked
// nothing, and could not have moved the gun no matter what the panel said.
//
// A local copy is the fix that cannot rot: no PLT entry, no relocation, nothing
// for inj to get wrong. Deliberately not named memcpy/strcmp - shadowing a libc
// name and hoping the compiler prefers the local one is the kind of trick that
// works until an optimiser decides otherwise.
static int vm_strcmp(const char* a, const char* b) {
    while (*a && *a == *b) { a++; b++; }
    return (int)(unsigned char)*a - (int)(unsigned char)*b;
}
static const char* vm_strstr(const char* h, const char* n) {
    if (!*n) return h;
    for (; *h; h++) {
        const char* a = h;
        const char* b = n;
        while (*a && *b && *a == *b) { a++; b++; }
        if (!*b) return h;
    }
    return nullptr;
}
static void vm_memcpy(void* d, const void* s, size_t n) {
    volatile unsigned char* p = (volatile unsigned char*)d;
    const unsigned char* q = (const unsigned char*)s;
    while (n--) *p++ = *q++;
}
static void vm_zero(void* d, size_t n) {
    volatile unsigned char* p = (volatile unsigned char*)d;
    while (n--) *p++ = 0;
}

// Unity object layout, the same in every il2cpp build: an array carries its
// length at 0x18 and its first element at 0x20, a string its length at 0x10 and
// its UTF-16 characters at 0x14.
static const uint64_t ARR_LEN = 0x18, ARR_DATA = 0x20, STR_LEN = 0x10, STR_CHARS = 0x14;

// ---------------------------------------------------------------- reading self

/**
 * Reads through process_vm_readv rather than dereferencing.
 *
 * Everything read below comes back from a managed call and should be valid, but
 * a wrong guess here is a SIGSEGV inside someone's match rather than a wrong
 * number on a panel. Same-process, same-uid, so no ptrace privilege is involved,
 * and unlike a snapshot of /proc/self/maps this can never be stale.
 */
static bool safe_read(uint64_t a, void* buf, size_t n) {
    if (!a || a < 0x1000 || !n) return false;
    struct iovec loc{buf, n};
    struct iovec rem{(void*)a, n};
    return process_vm_readv(getpid(), &loc, 1, &rem, 1, 0) == (ssize_t)n;
}

static uint64_t rd64(uint64_t a) { uint64_t v = 0; return safe_read(a, &v, 8) ? v : 0; }
// Fault-safe in-process store (mirrors safe_read) for raw il2cpp array element
// writes: Array.SetValue is stripped on this build, but the element storage is
// the same layout item()/rd64 already read.
static bool wr64(uint64_t a, uint64_t v) {
    struct iovec loc{&v, 8};
    struct iovec rem{(void*)a, 8};
    return process_vm_writev(getpid(), &loc, 1, &rem, 1, 0) == 8;
}
static int32_t  rd32(uint64_t a) { int32_t v = 0;  return safe_read(a, &v, 4) ? v : 0; }
static uint16_t rd16(uint64_t a) { uint16_t v = 0; return safe_read(a, &v, 2) ? v : 0; }

static long long now_ms() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static char* read_maps() {
    int fd = open("/proc/self/maps", O_RDONLY);
    if (fd < 0) return nullptr;
    size_t cap = 1 << 18, len = 0;
    char* b = (char*)malloc(cap);
    if (!b) { close(fd); return nullptr; }
    for (;;) {
        if (len + 4096 >= cap) {
            char* n = (char*)realloc(b, cap * 2);
            if (!n) break;
            b = n;
            cap *= 2;
        }
        ssize_t r = read(fd, b + len, cap - len - 1);
        if (r <= 0) break;
        len += (size_t)r;
    }
    close(fd);
    b[len] = 0;
    return b;
}

static inline int hexv(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}
static inline bool ishex(char c) { return hexv(c) >= 0; }

/**
 * The protection bits of the mapping an address falls in, 0 if it falls in none.
 *
 * The page that has to be made writable to plant the hook is inside a packed
 * libunity.so, where code and metadata share pages. So the change has to be
 * additive in both directions: adding PROT_WRITE must not drop PROT_EXEC from a
 * page the game executes, and putting the page back must not drop PROT_WRITE from
 * a page the game writes to. Both mistakes are a SIGSEGV a few frames later, in
 * the game's own code, with nothing pointing back here.
 */
static int page_prot(uintptr_t addr) {
    char* buf = read_maps();
    if (!buf) return 0;
    int prot = 0;
    char* p = buf;
    while (*p) {
        char* le = p;
        while (*le && *le != '\n') le++;
        if (*le) *le = 0;
        uint64_t st = 0, en = 0;
        int k = 0;
        while (ishex(p[k])) { st = st * 16 + (uint64_t)hexv(p[k]); k++; }
        if (p[k] == '-') {
            k++;
            while (ishex(p[k])) { en = en * 16 + (uint64_t)hexv(p[k]); k++; }
        }
        while (p[k] == ' ') k++;
        if (en > st && addr >= st && addr < en) {
            if (p[k] == 'r') prot |= PROT_READ;
            if (p[k] && p[k + 1] == 'w') prot |= PROT_WRITE;
            if (p[k] && p[k + 1] && p[k + 2] == 'x') prot |= PROT_EXEC;
            break;
        }
        p = le + 1;
    }
    free(buf);
    return prot;
}

/**
 * Whether an address can be branched to at all.
 *
 * Everything below is a pointer that came out of an offset table or out of a
 * struct field read by guesswork, and every one of them ends up in a blr. When a
 * guess is wrong the value is not usually null - it is a plausible number that
 * points at metadata, or at a page that is readable and nothing more. Checking the
 * mapping first turns a crash inside someone's match into a log line, which is the
 * whole difference between a bug that can be fixed and a bug that can only be
 * reproduced.
 */
static bool callable(const void* p) {
    return p && (page_prot((uintptr_t)p) & PROT_EXEC) != 0;
}

// ------------------------------------------------------- RVA -> live address

/**
 * Turns a file-relative RVA from il2cpp.hpp into an address in this process.
 *
 * base + rva is wrong for this library: the loader maps each segment at its own
 * alignment, so file offsets and virtual offsets drift apart. Every mapping of
 * libunity.so is collected with the file offset the kernel reports, the load bias
 * is the address of the mapping at file offset 0, and an RVA is then looked up in
 * whichever segment actually covers it. Executable wins ties, because a code RVA
 * can also fall inside a read-only mapping of the same bytes.
 *
 * The "forge" flag drops a mapping at file offset 0 that reaches the end of the
 * file - that is a whole-file mapping the packer leaves behind, and taking it as
 * the load bias puts every resolved pointer in the wrong place.
 */
struct lib_seg { uint64_t va, foff, size, vaddr; bool exec, forge; };
// A fixed array rather than a vector, for three reasons that all came out of one
// crash hunt. A vector needs operator new, which drags in the C++ runtime and its
// exception path; it needs memmove, which is one of the ifunc names above; and it
// needs a static constructor, which lands in .init_array *after* the entry that
// starts the poll thread - so the thread could be inside build_segs() while the
// initialiser zeroed the three pointers out from under it. Nothing to race now.
#define MAX_SEGS 32
static lib_seg g_segs[MAX_SEGS];
static int     g_nsegs;

static void build_segs() {
    g_nsegs = 0;
    char* buf = read_maps();
    if (!buf) return;
    char* p = buf;
    while (*p) {
        char* le = p;
        while (*le && *le != '\n') le++;
        if (*le) *le = 0;
        uint64_t st = 0, en = 0, off = 0;
        int k = 0;
        while (ishex(p[k])) { st = st * 16 + (uint64_t)hexv(p[k]); k++; }
        if (p[k] == '-') {
            k++;
            while (ishex(p[k])) { en = en * 16 + (uint64_t)hexv(p[k]); k++; }
        }
        while (p[k] == ' ') k++;
        bool exec = (p[k] == 'r' && p[k + 2] == 'x');
        for (int i = 0; i < 4 && p[k]; i++) k++;
        while (p[k] == ' ') k++;
        while (ishex(p[k])) { off = off * 16 + (uint64_t)hexv(p[k]); k++; }
        const char* q = p;
        while (*q && *q != '/') q++;
        if (*q == '/' && vm_strstr(q, UNITY_LIB) && en > st && g_nsegs < MAX_SEGS)
            g_segs[g_nsegs++] = lib_seg{st, off, en - st, 0, exec, false};
        p = le + 1;
    }
    free(buf);

    uint64_t max_end = 0;
    for (int i = 0; i < g_nsegs; i++)
        if (g_segs[i].foff + g_segs[i].size > max_end) max_end = g_segs[i].foff + g_segs[i].size;

    uint64_t load_bias = 0;
    for (int i = 0; i < g_nsegs; i++) {
        lib_seg& s = g_segs[i];
        if (s.foff == 0) {
            if (max_end && s.foff + s.size == max_end) s.forge = true;
            if (!s.forge) load_bias = s.va;
        }
    }
    if (!load_bias)
        for (int i = 0; i < g_nsegs; i++)
            if (g_segs[i].foff == 0 && !g_segs[i].forge &&
                (!load_bias || g_segs[i].va < load_bias)) load_bias = g_segs[i].va;
    if (!load_bias && g_nsegs) load_bias = g_segs[0].va;

    for (int i = 0; i < g_nsegs; i++)
        if (!g_segs[i].forge) g_segs[i].vaddr = g_segs[i].va - load_bias;
}

/**
 * Deliberately not std::call_once: the payload starts before the game has
 * finished loading libunity.so, and a table built once while it was still absent
 * would stay empty for the life of the process.
 *
 * Only ever returns an address inside an executable mapping. It used to fall back
 * to a non-executable one when no code segment covered the RVA, and every pointer
 * il2cpp::init_api hands out gets *called* - the first one blind, domain_get(), on
 * this thread. A packed library that is halfway through unpacking has its code
 * mapped r-- for a while, so that fallback was a branch into unexecutable memory:
 * instant SIGSEGV in a process that leaves no tombstone. Returning nothing costs
 * one 500 ms retry, which is the correct price.
 */
static void* segment_resolve_rva(uint64_t rva) {
    if (!g_nsegs) build_segs();
    for (int i = 0; i < g_nsegs; i++) {
        const lib_seg& s = g_segs[i];
        if (s.forge || !s.size || !s.exec) continue;
        if (rva < s.vaddr || rva >= s.vaddr + s.size) continue;
        return (void*)(s.va + (rva - s.vaddr));
    }
    return nullptr;
}

struct lf_s { const char* name; uintptr_t addr; };
static int lf_cb(struct dl_phdr_info* i, size_t s, void* d) {
    (void)s;
    lf_s* f = (lf_s*)d;
    if (i->dlpi_name && vm_strstr(i->dlpi_name, f->name)) { f->addr = i->dlpi_addr; return 1; }
    return 0;
}
static uintptr_t find_lib(const char* n) {
    lf_s f{n, 0};
    dl_iterate_phdr(lf_cb, &f);
    return f.addr;
}

// ------------------------------------------------------------ il2cpp bindings

/**
 * A MethodInfo carries its native entry point at +0x8. Reading it is how a
 * managed method becomes a callable pointer; writing it is how one gets hooked.
 * The MethodInfo struct declared in il2cpp.hpp puts the field at 0 and is wrong
 * for this build, so the numeric offset from the table is used instead.
 *
 * Read through safe_read, not dereferenced: a name that is missing from an
 * obfuscated build comes back as a plausible-looking pointer often enough that
 * one raw load here is a crash in someone's match. And the value read back is
 * only accepted if it lands in executable memory - a MethodInfo that is not one
 * yields a number, and that number is about to be called.
 */
static void* mp(const void* m) {
    if (!m) return nullptr;
    void* p = (void*)rd64((uintptr_t)m + il2cpp::offset::il2cpp_method_pointer);
    return callable(p) ? p : nullptr;
}

/**
 * Walks up the class hierarchy, because get_enabled lives on Behaviour and
 * get_name on Object while the object in hand is a Camera. Match the managed
 * argument count: setters take one argument, getters and LateUpdate take zero.
 */
static const Il2CppMethod* find_method(Il2CppClass* c, const char* name, int argc) {
    for (Il2CppClass* k = c; k; k = il2cpp::class_get_parent ? il2cpp::class_get_parent(k) : nullptr) {
        if (il2cpp::class_get_method_from_name) {
            const Il2CppMethod* m = il2cpp::class_get_method_from_name(k, name, argc);
            if (m) return m;
        }
        if (!il2cpp::class_get_methods || !il2cpp::method_get_name ||
            !il2cpp::method_get_param_count) continue;
        void* it = nullptr;
        while (const Il2CppMethod* m = il2cpp::class_get_methods(k, &it)) {
            const char* nm = il2cpp::method_get_name(m);
            if (nm && vm_strcmp(nm, name) == 0 &&
                (int)il2cpp::method_get_param_count(m) == argc) return m;
        }
    }
    return nullptr;
}

// Every one of these is a Unity name, so none of them moves when the game
// updates. get_allCameras is the only allocating call in the set.
static void* (*cam_all)();             // Camera.get_allCameras -> Camera[]
static void* (*cam_main)();            // Camera.get_main
static float (*cam_getfov)(void*);     // Camera.get_fieldOfView
static void  (*cam_setfov)(void*, float);
static const Il2CppMethod *cam_fov_get, *cam_fov_set;
static float (*cam_getdepth)(void*);   // Camera.get_depth
static bool  (*cam_geten)(void*);      // Behaviour.get_enabled
static void* (*cam_getname)(void*);    // Object.get_name -> Il2CppString*

// ------------------------------------------------------------------ live state

// Config, camera state and hook lifecycle share one lock across both threads.
static pthread_mutex_t state_mutex = PTHREAD_MUTEX_INITIALIZER;
static float g_want_fov = 0.f;   // 0 = off, restore and stop writing
static int   g_want_idx = -1;    // -1 = auto pick, else index in the list
// 0 = safe mode: resolve everything and report the camera list, but never touch
// LateUpdate. Splits "the injection killed the game" from "the hook killed it",
// which is otherwise one symptom with two causes.
//
// Off until the cfg says otherwise, and that is deliberate. It used to default
// to armed, so back when the cfg was unreadable the hook went in on every press
// including the one that asked for safe mode - the one mode that would have told
// us which half was fatal was the one mode that could not happen. An unreadable
// cfg now costs a feature that does nothing instead of a match.
static int   g_want_hook = 0;

struct cam_row { char name[40]; float fov, depth; int en, ismain; };
static cam_row g_rows[16];
static int  g_nrows;
static char g_target[40];
static int  g_target_main;
static int  g_ticks;            // how many times the hook has run
static int  g_api_ok, g_hooked;
static Il2CppImage* g_core_image;
static bool g_camera_ok;
static char g_camera_reason[192] = "not resolved";
static const char* g_api_reason = "not started";
static const char* g_hook_reason = "not requested";
static const char* g_stage = "worker starting";
static void write_report();

// Publish before an unverified runtime call: a stalled call must not erase the
// last reachable stage. No IL2CPP calls are made by write_report itself.
static void report_stage(const char* stage) {
    g_stage = stage;
    write_report();
}

static const Il2CppMethod* lu_mi;
static void* lu_mp;

/**
 * Resolves the shared il2cpp API. Retried until it succeeds,
 * because the payload is injected before the game has finished starting: the
 * assemblies, and sometimes libunity.so itself, are not there yet.
 *
 * Metadata calls (class_from_name, class_get_methods) are safe on this thread.
 * The calls that touch managed objects - get_allCameras and set_fieldOfView -
 * are not, and only ever run inside the LateUpdate hook.
 */
// api_init runs twice a second until it succeeds, so a plain log line in it would
// be a flood. Only a *changed* reason is worth a line - the pointer compare is
// enough because every reason below is a literal in this translation unit.
static bool api_fail(const char* why) {
    g_api_reason = why;
    static const char* last;
    if (last != why) { last = why; LG("api_init stuck at %s", why); }
    return false;
}

static const char* method_state(const Il2CppMethod* method, const void* entry) {
    return !method ? "missing" : entry ? "ok" : "entry not executable";
}

#include "visuals.hpp"
#include "client_skins.hpp"

static Vec3 g_want_offset{};
static Il2CppClass* vm_camera_class;
static uintptr_t vm_camera_type;
static visuals::Method vm_find_cameras, vm_get_go, vm_active;
static visuals::Method vm_get_transform, vm_get_position, vm_set_position;
static void* (*vm_find_icall)(void*);

static void* find_cameras() {
    if (!vm_camera_type && visuals::init_lifetime())
        vm_camera_type = visuals::retain(il2cpp::type_get_object(il2cpp::class_get_type(vm_camera_class)));
    void* type = visuals::target(vm_camera_type);
    if (!type) return nullptr;
    void* args[] = {type};
    return vm_find_cameras ? visuals::call(vm_find_cameras, nullptr, args) :
        vm_find_icall ? vm_find_icall(type) : nullptr;
}

static bool camera_active(void* camera) {
    if (!visuals::living(camera) || (cam_geten && !cam_geten(camera))) return false;
    if (!vm_get_go || !vm_active) return cam_all != find_cameras;
    void* go = visuals::call(vm_get_go, camera);
    bool active = false;
    return go && visuals::value(vm_active, go, active) && active;
}

// Camera support is optional: skins and material chams only need the shared
// IL2CPP API and LateUpdate. Keep their startup independent of FOV methods.
static bool bind_unity_methods(Il2CppImage* im) {
    report_stage("Camera class");
    Il2CppClass* ca = il2cpp::class_from_name(im, "UnityEngine", "Camera");
    report_stage("Camera methods");
    const Il2CppMethod* all = find_method(ca, "get_allCameras", 0);
    cam_all      = (void* (*)())mp(all);
    cam_main     = (void* (*)())mp(find_method(ca, "get_main", 0));
    cam_fov_get  = find_method(ca, "get_fieldOfView", 0);
    cam_fov_set  = find_method(ca, "set_fieldOfView", 1);
    cam_getfov   = (float (*)(void*))mp(cam_fov_get);
    cam_setfov   = (void (*)(void*, float))mp(cam_fov_set);
    cam_getdepth = (float (*)(void*))mp(find_method(ca, "get_depth", 0));
    cam_geten    = (bool (*)(void*))mp(find_method(ca, "get_enabled", 0));
    cam_getname  = (void* (*)(void*))mp(find_method(ca, "get_name", 0));
    auto component = il2cpp::class_from_name(im, "UnityEngine", "Component");
    auto go = il2cpp::class_from_name(im, "UnityEngine", "GameObject");
    auto transform = il2cpp::class_from_name(im, "UnityEngine", "Transform");
    vm_get_go = find_method(component, "get_gameObject", 0);
    vm_active = find_method(go, "get_activeInHierarchy", 0);
    vm_get_transform = find_method(component, "get_transform", 0);
    vm_get_position = find_method(transform, "get_localPosition", 0);
    vm_set_position = find_method(transform, "set_localPosition", 1);
    if (!mp(vm_get_transform)) vm_get_transform = nullptr;
    if (!mp(vm_get_position)) vm_get_position = nullptr;
    if (!mp(vm_set_position)) vm_set_position = nullptr;
    vm_camera_class = ca;
    if (!cam_all && ca) {
        auto resources = il2cpp::class_from_name(im, "UnityEngine", "Resources");
        auto internal = il2cpp::class_from_name(im, "UnityEngine", "ResourcesAPIInternal");
        vm_find_cameras = visuals::method(resources, "FindObjectsOfTypeAll", 1, "System.Type");
        if (!vm_find_cameras) vm_find_cameras = visuals::method(internal, "FindObjectsOfTypeAll", 1, "System.Type");
        vm_find_icall = nullptr;
        if (!vm_find_cameras) vm_find_icall = (decltype(vm_find_icall))visuals::icall(
            "UnityEngine.ResourcesAPIInternal::FindObjectsOfTypeAll(System.Type)");
        if ((vm_find_cameras || vm_find_icall) && mp(vm_get_go) && mp(vm_active)) cam_all = find_cameras;
    }
    g_camera_ok = cam_all && cam_setfov && cam_getfov;
    snprintf(g_camera_reason, sizeof g_camera_reason,
             "class=%s get_allCameras=%s get_fieldOfView=%s set_fieldOfView=%s resources=%s xyz=%s",
             ca ? "ok" : "missing", method_state(all, (void*)cam_all),
             method_state(cam_fov_get, (void*)cam_getfov),
             method_state(cam_fov_set, (void*)cam_setfov),
             cam_all == find_cameras ? "ok" : "off",
             mp(vm_get_transform) && mp(vm_get_position) && mp(vm_set_position) ? "ok" : "missing");
    LG("camera: %s", g_camera_reason);
    g_api_ok = 1;
    g_api_reason = "ready";
    g_stage = g_hooked ? "Unity frames running" : "shared API ready";
    return true;
}

static bool api_init() {
    if (g_api_ok) return true;
    if (!find_lib(UNITY_LIB)) return api_fail("libunity not mapped");
    build_segs();
    if (!g_nsegs) return api_fail("no segments");
    il2cpp::resolve_rva = segment_resolve_rva;
    il2cpp::init_api(0);
    if (!il2cpp::domain_get || !il2cpp::domain_assembly_open || !il2cpp::assembly_get_image ||
        !il2cpp::class_from_name || !il2cpp::class_get_methods ||
        !il2cpp::method_get_name || !il2cpp::method_get_param_count) return api_fail("rva table");
    // domain_get is the first thing called at an address nobody has verified. Every
    // pointer in the table came from an RVA cut for one build of the game against a
    // library the packer rearranges, so the sanity check happens here, before the
    // branch, not after it in a logcat nobody can read because the process is gone.
    if (!callable((void*)il2cpp::domain_get)) return api_fail("domain_get not executable");
    report_stage("domain_get");
    Il2CppDomain* d = il2cpp::domain_get();
    if (!d) return api_fail("domain_get");
    // Once. This runs twice a second until it succeeds, and an il2cpp thread is
    // allocated and registered with the GC on every call - a slow leak, and this
    // thread only ever needs to be attached one time.
    static int attached;
    if (!attached && il2cpp::thread_attach) {
        report_stage("thread_attach");
        if (!il2cpp::thread_attach(d)) return api_fail("thread_attach");
        attached = 1;
    }
    report_stage("CoreModule");
    Il2CppAssembly* a = il2cpp::domain_assembly_open(d, "UnityEngine.CoreModule");
    if (!a) return api_fail("CoreModule");
    Il2CppImage* im = il2cpp::assembly_get_image(a);
    if (!im) return api_fail("CoreModule image");
    g_core_image = im;
    return bind_unity_methods(im);
}

// -------------------------------------------------- the camera list (Unity thread)

static int cam_list(void** out, int cap) {
    if (!cam_all) return 0;
    uint64_t a = (uint64_t)cam_all();
    if (!a) return 0;
    int n = (int)rd64(a + ARR_LEN);
    if (n <= 0 || n > 256) return 0;
    int k = 0;
    for (int i = 0; i < n && k < cap; i++) {
        uint64_t c = rd64(a + ARR_DATA + 8 * i);
        if (c && camera_active((void*)c)) out[k++] = (void*)c;
    }
    return k;
}

static void cam_name(void* o, char* buf, size_t cap) {
    buf[0] = 0;
    if (!cam_getname || !o) return;
    uint64_t s = (uint64_t)cam_getname(o);
    if (!s) return;
    int len = rd32(s + STR_LEN);
    if (len <= 0) return;
    if ((size_t)len > cap - 1) len = (int)(cap - 1);
    for (int i = 0; i < len; i++) {
        uint16_t ch = rd16(s + STR_CHARS + 2 * i);
        buf[i] = (ch >= 32 && ch < 127) ? (char)ch : '?';
    }
    buf[len] = 0;
}

static bool cam_hinted(const char* n) {
    static const char* h[] = {"weapon", "viewmodel", "arms", "hand", "gun", "fps", "firstperson"};
    char lo[40];
    size_t i = 0;
    for (; n[i] && i < sizeof(lo) - 1; i++) lo[i] = (n[i] >= 'A' && n[i] <= 'Z') ? (char)(n[i] + 32) : n[i];
    lo[i] = 0;
    for (size_t j = 0; j < sizeof(h) / sizeof(*h); j++) if (vm_strstr(lo, h[j])) return true;
    return false;
}

/**
 * Snapshots the cameras and picks the weapon one.
 *
 * Camera.main is always excluded: it draws the world, and raising its FOV zooms
 * the whole screen instead of shrinking the gun. A name hint wins, otherwise the
 * highest depth - the gun is composited on top of the world, so its camera draws
 * last. A manual index from the cfg overrides both, for when the heuristic misses.
 */
static void* cam_scan() {
    void* cams[16];
    int n = cam_list(cams, 16);
    uint64_t local = visuals::local_player();
    void* mainc = local ? (void*)rd64(rd64(local+0xE8)+0x20) : nullptr;
    if (!mainc) mainc = cam_main ? cam_main() : nullptr;
    g_nrows = 0;
    for (int i = 0; i < n; i++) {
        cam_row& r = g_rows[i];
        cam_name(cams[i], r.name, sizeof r.name);
        r.fov    = cam_getfov   ? cam_getfov(cams[i])   : 0.f;
        r.depth  = cam_getdepth ? cam_getdepth(cams[i]) : 0.f;
        r.en     = cam_geten    ? (cam_geten(cams[i]) ? 1 : 0) : -1;
        r.ismain = (mainc && cams[i] == mainc) ? 1 : 0;
        g_nrows = i + 1;
    }
    int want = g_want_idx, pick = -1;
    if (want >= 0 && want < n) {
        pick = want;
    } else {
        for (int i = 0; i < n; i++)
            if (!g_rows[i].ismain && cam_hinted(g_rows[i].name)) { pick = i; break; }
        if (pick < 0 && mainc) {
            float bd = -1e9f;
            for (int i = 0; i < n; i++)
                if (!g_rows[i].ismain && g_rows[i].depth > bd) { bd = g_rows[i].depth; pick = i; }
        }
    }
    if (pick < 0) { g_target[0] = 0; g_target_main = 0; return nullptr; }
    vm_memcpy(g_target, g_rows[pick].name, sizeof g_target);
    g_target_main = g_rows[pick].ismain;
    return cams[pick];
}

// ------------------------------------------------ the per-frame tick and the hook

static uintptr_t vm_camera;
static float vm_original_fov;
static bool vm_have_original;
static uintptr_t vm_transform;
static Vec3 vm_original_position{}, vm_applied_position{};
static bool vm_position_changed;
static const char* vm_status = "off";

static bool same_position(Vec3 a, Vec3 b) {
    return std::fabs(a.x-b.x)<.00001f && std::fabs(a.y-b.y)<.00001f && std::fabs(a.z-b.z)<.00001f;
}

static bool vm_restore_position() {
    if (!vm_transform) return true;
    bool ok = false;
    void* transform = visuals::target(vm_transform, &ok);
    if (!ok) return false;
    bool live = visuals::living(transform, &ok);
    if (!ok) return false;
    if (live && vm_position_changed) {
        Vec3 current{};
        if (!visuals::value(vm_get_position, transform, current)) return false;
        // Preserve an animation update that has already replaced our position.
        if (same_position(current, vm_applied_position)) {
            void* args[] = {&vm_original_position};
            visuals::call(vm_set_position, transform, args, &ok);
            if (!ok) return false;
        }
    }
    visuals::release(vm_transform); vm_position_changed = false;
    return true;
}

static bool vm_apply_position(void* camera) {
    if (same_position(g_want_offset, {})) return vm_restore_position();
    if (!vm_get_transform || !vm_get_position || !vm_set_position) return false;
    if (!vm_transform) vm_transform = visuals::retain(visuals::call(vm_get_transform, camera));
    void* transform = visuals::target(vm_transform);
    Vec3 current{};
    if (!visuals::living(transform) || !visuals::value(vm_get_position, transform, current) || !finite_vec(current)) return false;
    if (!vm_position_changed || !same_position(current, vm_applied_position)) vm_original_position = current;
    // Moving the hands camera in the opposite direction moves the weapon as requested.
    Vec3 position{vm_original_position.x-g_want_offset.x, vm_original_position.y-g_want_offset.y,
                  vm_original_position.z-g_want_offset.z};
    if (same_position(current, position)) return true;
    void* args[] = {&position}; bool ok = false;
    visuals::call(vm_set_position, transform, args, &ok);
    if (ok) { vm_applied_position = position; vm_position_changed = true; }
    return ok;
}

static bool vm_restore_camera() {
    if (!vm_restore_position()) return false;
    if (!vm_camera) return true;
    bool ok = false;
    void* camera = visuals::target(vm_camera, &ok);
    if (!ok) return false;
    bool live = visuals::living(camera, &ok);
    if (!ok) return false;
    if (live && vm_have_original) {
        void* args[] = {&vm_original_fov};
        visuals::call(cam_fov_set, camera, args, &ok);
        if (!ok) return false;
    }
    visuals::release(vm_camera);
    vm_have_original = false;
    return true;
}

static bool hook_requested() {
    return clientskins::requested() || (g_want_hook && g_want_fov > 0.f) ||
            ((__atomic_load_n(&vis_flags, __ATOMIC_ACQUIRE) & (ESP_SKELETON | ESP_CHAMS)) &&
             vis_now() <= __atomic_load_n(&vis_expires, __ATOMIC_ACQUIRE));
}
static void unhook_lu();

/**
 * ponytail: get_allCameras allocates a managed array, so the list is rebuilt on a
 * 2 s clock and the chosen camera is held between scans. Time, not a frame count:
 * LateUpdate fires once per PlayerController per frame, so a counter would speed
 * up as the lobby fills. A camera that gets recreated is picked up by the next scan.
 *
 * The FOV the game itself had is cached and put back when the slider goes to 0, so
 * a wrong pick costs a slider move rather than a game restart.
 */
static void vm_tick() {
    float want = g_want_hook ? g_want_fov : 0.f;
    if (want <= 0.f) { vm_status = vm_restore_camera() ? "off" : "restore pending"; return; }
    if (!g_api_ok || !cam_all || !cam_setfov || !cam_getfov || !visuals::init_lifetime()) {
        vm_status = "camera API unavailable"; return;
    }
    bool ok = false;
    void* cam = visuals::target(vm_camera, &ok);
    if (!ok) return;
    static int last_idx = -2;
    static long long last;
    long long t = now_ms();
    if (!last || last_idx != g_want_idx || t - last >= 2000) {
        void* nc = cam_scan();
        if (g_target_main) nc = nullptr;
        if (nc != cam) {
            if (!vm_restore_camera()) return;
            vm_camera = visuals::retain(nc);
            cam = vm_camera ? nc : nullptr;
        }
        last = t;
        last_idx = g_want_idx;
    }
    if (!cam) { vm_status = "hands camera not found"; return; }
    if (!visuals::living(cam, &ok)) {
        if (ok && vm_restore_camera()) last = 0;
        return;
    }
    float current = 0;
    if (!visuals::value(cam_fov_get, cam, current) || !std::isfinite(current)) return;
    if (!vm_have_original) { vm_original_fov = current; vm_have_original = true; }
    if (current != want) {
        void* args[] = {&want};
        visuals::call(cam_fov_set, cam, args, &ok);
        if (!ok) { vm_status = "FOV write failed"; return; }
    }
    vm_status = vm_apply_position(cam) ? "applied" : "FOV applied; XYZ unavailable";
}

/**
 * ponytail: no local-player check, so no game offsets at all. LateUpdate runs once
 * per player per frame, but the rescan is on a clock and the write is skipped when
 * the value already matches, so the extra calls cost nothing.
 *
 * Both arguments are forwarded. An il2cpp instance method is compiled to
 * (void* __this, const MethodInfo* method), so x1 is live on entry; a hook taking
 * one argument is free to clobber it and hand LateUpdate a garbage method.
 */
static void hk_lu(void* p, void* mi) {
    // Only the first frame, and in three parts on purpose. If the game dies inside
    // the hook these lines say which third it got to: entered, the game's own
    // LateUpdate returned, our tick returned. A missing line is the answer.
    static int first = 1;
    int f = first;
    if (f) { first = 0; LG("hook entered, this=%p mi=%p", p, mi); }
    // Acquire, paired with the release in hook_lu. If this is somehow still null the
    // only safe thing is to do nothing: LateUpdate does not run this frame, which
    // costs one frame of animation, where a branch to zero costs the process.
    void* orig = __atomic_load_n(&lu_mp, __ATOMIC_ACQUIRE);
    if (!orig) { if (f) LG("hook entered with no original - skipped"); return; }
    ((void(*)(void*, void*))orig)(p, mi);   // original first: the animator has already run
    if (f) LG("original LateUpdate returned");
    pthread_mutex_lock(&state_mutex);
    g_ticks++;
    if (g_hooked) {
        if (g_ticks == 1) report_stage("first Unity frame");
        // First-frame breadcrumbs to logcat (tag ANODIZE). If chams freezes the
        // render thread, the report file is frozen behind state_mutex and useless;
        // logcat survives. The last "-> X" printed names the call that hung.
        if (f) LG("-> vm_tick");
        vm_tick();
        if (f) LG("-> visuals::tick");
        visuals::tick(p);
        if (f) LG("-> clientskins::tick");
        if (g_ticks == 1) report_stage("client skin initialization");
        clientskins::tick(p);
        if (f) LG("-> trio done");
        g_stage = "Unity frames running";
        if (!hook_requested() && !vm_camera && !visuals::pending_restore() && !clientskins::pending_restore()) unhook_lu();
    }
    pthread_mutex_unlock(&state_mutex);
    if (f) LG("first tick done");
}

// Same rate limit as api_fail, and its own last-reason for the same reason: one
// shared slot would make the two functions log each other's line every cycle.
static void lu_fail(const char* why) {
    g_hook_reason = why;
    static const char* last;
    if (last != why) { last = why; LG("resolve_lu stuck at %s", why); }
}

static void resolve_lu() {
    if (lu_mi || !il2cpp::domain_get || !il2cpp::domain_assembly_open ||
        !il2cpp::assembly_get_image || !il2cpp::class_from_name) return;
    report_stage("PlayerController hook lookup");
    Il2CppDomain* d = il2cpp::domain_get();
    if (!d) return lu_fail("domain_get");
    Il2CppAssembly* a = il2cpp::domain_assembly_open(d, "Assembly-CSharp");
    if (!a) return lu_fail("Assembly-CSharp");
    Il2CppImage* gi = il2cpp::assembly_get_image(a);
    if (!gi) return lu_fail("Assembly-CSharp image");
    // Class names survive obfuscation even though member names do not.
    Il2CppClass* pc = il2cpp::class_from_name(gi, "Axlebolt.Standoff.Player", "PlayerController");
    if (!pc) return lu_fail("class PlayerController");
    lu_mi = find_method(pc, "LateUpdate", 0);
    if (!lu_mi) return lu_fail("method LateUpdate");
    LG("LateUpdate MethodInfo %p mp %p", (void*)lu_mi,
       (void*)rd64((uintptr_t)lu_mi + il2cpp::offset::il2cpp_method_pointer));
}

/**
 * Swaps the methodPointer for our own. Only the 8 bytes at +0x8 are written, and
 * they are 8-aligned, so the single page that slot sits in is the whole exposure -
 * no need to guess whether the struct straddles a boundary.
 *
 * The page keeps every right it already had. It sits inside a packed libunity.so,
 * where one page can hold metadata and code at once, so PROT_WRITE is added to the
 * rights already there instead of replacing them, and they are put back as soon as
 * the pointer is in. Dropping PROT_EXEC here and leaving it dropped is a SIGSEGV
 * the next time the game runs anything that happens to live on the same page.
 *
 * lu_mp is stored before the slot is written: the Unity thread can enter the hook
 * on the very next frame, and a hook whose original pointer is not there yet
 * branches to null.
 */
static uintptr_t lu_page;
static long lu_page_size;
static int lu_page_protection;
static bool lu_page_open;

static bool restore_lu_page() {
    if (!lu_page_open) return true;
    if (mprotect((void*)lu_page, (size_t)lu_page_size, lu_page_protection) != 0) return false;
    lu_page_open = false;
    return true;
}

static bool swap_lu(void* expected, void* replacement) {
    if (!restore_lu_page()) return false;
    uintptr_t slot = (uintptr_t)lu_mi + il2cpp::offset::il2cpp_method_pointer;
    long pg = sysconf(_SC_PAGESIZE);
    if (pg <= 0 || slot % alignof(void*) != 0) return false;
    uintptr_t page = slot & ~(uintptr_t)(pg - 1);
    int old = page_prot(slot);
    if (!old) return false;
    if (!(old & PROT_WRITE)) {
        if (mprotect((void*)page, (size_t)pg, old | PROT_WRITE) != 0) return false;
        lu_page = page; lu_page_size = pg; lu_page_protection = old; lu_page_open = true;
    }
    bool swapped = __atomic_compare_exchange_n((void**)slot, &expected, replacement, false,
                                               __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
    if (swapped) __builtin___clear_cache((char*)slot, (char*)slot + sizeof(void*));
    if (!restore_lu_page()) LG("LateUpdate page protection restore pending, errno %d", errno);
    return swapped;
}

static void unhook_lu() {
    void* original = __atomic_load_n(&lu_mp, __ATOMIC_ACQUIRE);
    if (!g_hooked || !original || !swap_lu((void*)hk_lu, original)) return;
    g_hooked = 0;
    // Keep lu_mp and the library alive for callbacks already dispatched by Unity.
    LG("original LateUpdate restored");
}

static void hook_lu() {
    if (!lu_mi || g_hooked || !hook_requested()) return;
    uintptr_t slot = (uintptr_t)lu_mi + il2cpp::offset::il2cpp_method_pointer;
    void* original = (void*)rd64(slot);
    if (!callable(original) || original == (void*)hk_lu) {
        lu_fail("LateUpdate pointer invalid"); return;
    }
    void* previous = __atomic_load_n(&lu_mp, __ATOMIC_ACQUIRE);
    if (previous && previous != original) { lu_fail("LateUpdate pointer changed externally"); return; }
    __atomic_store_n(&lu_mp, original, __ATOMIC_RELEASE);
    if (!swap_lu(original, (void*)hk_lu)) { lu_fail("LateUpdate slot write failed"); return; }
    g_hooked = 1;
    g_hook_reason = "waiting for Unity frame";
    g_stage = "waiting for Unity frame";
    LG("hook planted: slot %p was %p now %p", (void*)slot, original, (void*)hk_lu);
}

// ------------------------------------------------------------- the two-file link

/**
 * "<fov> [camIndex] [hook]", 0 means off. A half-written file is simply not parsed
 * and the previous value stands, so a slider moving while this reads costs one cycle.
 *
 * The hook digit enables FOV writes. Disabling it restores the camera, then removes
 * the hook once model visuals also finish restoring their state.
 * Missing means 1, so an old two-number cfg keeps working.
 */
static void read_cfg() {
    int fd = open(CFG_PATH, O_RDONLY);
    if (fd < 0) {
        // The failure that cost three matches. Logged with errno because EACCES here
        // means the label or the directory is wrong, ENOENT means the app never wrote.
        static int said;
        if (!said) { said = 1; LG("cfg open failed: %s errno %d", CFG_PATH, errno); }
        return;
    }
    char b[160];
    ssize_t r = read(fd, b, sizeof b - 1);
    close(fd);
    if (r <= 0) return;
    b[r] = 0;
    char* e = nullptr;
    float f = strtof(b, &e);
    if (e == b) return;
    char* e2 = nullptr;
    long i = strtol(e, &e2, 10);
    char* e3 = nullptr;
    long h = strtol(e2, &e3, 10);
    if (!std::isfinite(f) || f < 0.f || f > 179.f) return;
    Vec3 offset{};
    char* next = e3;
    while (*next == ' ' || *next == '\t' || *next == '\r' || *next == '\n') next++;
    if (*next) {
        float* values[] = {&offset.x, &offset.y, &offset.z};
        for (float* v : values) {
            char* end = nullptr; *v = strtof(next, &end);
            if (end == next || !std::isfinite(*v) || std::fabs(*v) > 1.f) return;
            next = end;
        }
        while (*next == ' ' || *next == '\t' || *next == '\r' || *next == '\n') next++;
        if (*next) return;
    }
    g_want_fov = f;
    g_want_offset = offset;
    g_want_idx = (e2 != e && i >= -1 && i < 16) ? (int)i : -1;
    g_want_hook = (e3 != e2 && h == 0) ? 0 : 1;
    static float sf = -1.f;
    static int si = -2, sh = -1;
    if (sf != f || si != g_want_idx || sh != g_want_hook) {
        sf = f; si = g_want_idx; sh = g_want_hook;
        LG("cfg fov %.1f idx %d hook %d", (double)f, g_want_idx, g_want_hook);
    }
}

/**
 * The camera list is the whole diagnosis channel: the app cats this back into the
 * status strip and the tester photographs it. ASCII only, so nothing depends on
 * which charset the Java side reads with. "api no" and "hook no" are different
 * failures - an API that never resolved versus a hook that never ticked.
 *
 * The state mutex also keeps the camera rows consistent while the poller reads them.
 */
static void put(char* b, int cap, int* n, const char* f, ...)
        __attribute__((format(printf, 4, 5)));
static void put(char* b, int cap, int* n, const char* f, ...) {
    if (*n >= cap - 1) return;
    va_list ap;
    va_start(ap, f);
    int r = vsnprintf(b + *n, (size_t)(cap - *n), f, ap);
    va_end(ap);
    if (r > 0) *n += (r > cap - 1 - *n) ? cap - 1 - *n : r;
}

static void write_report() {
    char b[PAYLOAD_REPORT_CAPACITY];
    int n = 0, cap = (int)sizeof b;
    put(b, cap, &n, "anodize viewmodel visuals9 %s\napi %s  hook %s  ticks %d\n",
        PAYLOAD_SKINS_VERSION, g_api_ok ? "ok" : "no", g_hooked ? "ok" : "no", g_ticks);
    put(b, cap, &n, "pid %d\n",getpid());
    put(b, cap, &n, "build skins-trace-v26-names\ncamera api %s: %s\n",
        g_camera_ok ? "ok" : "no", g_camera_reason);
    put(b, cap, &n, "skins: cfg=%d lease=%s revision=%llu api=%s hook=%s ticks=%d applied=%d\n",
        clientskins::config.count, clientskins::requested() ? "on" : "off",
        clientskins::config.revision,
        g_api_ok ? "ok" : "no", g_hooked ? "ok" : "no", g_ticks, clientskins::applied_count);
    put(b, cap, &n, "stage: %s; %s\n", g_stage,
        !g_api_ok ? g_api_reason : !g_hooked && hook_requested() ? g_hook_reason : clientskins::status);
    put(b, cap, &n, "scan: local_ticks=%llu renderers=%d fps=%d matched=%d\n",
        clientskins::local_ticks, clientskins::renderer_count, clientskins::fps_count, clientskins::matched_count);
    put(b, cap, &n, "unity lifetime: %s\nchams api: %s\nchams detail: %s\nchams bundle: %s\nchams methods: %s\nskins api: %s\n",
        visuals::lifetime_error, visuals::api_error, visuals::chams_error, visuals::chams_diag, visuals::bundle_methods, clientskins::api_error);
    int shader = __atomic_load_n(&visuals::shader_status, __ATOMIC_ACQUIRE);
    put(b, cap, &n, "chams: %s  models %d  applied %d\n",
        shader == 1 ? visuals::shader_names[0] :
            shader == -2 ? "Unity API missing" : shader == -1 ? "no supported shader" : "waiting",
        __atomic_load_n(&visuals::model_count, __ATOMIC_ACQUIRE),
        __atomic_load_n(&visuals::applied_count, __ATOMIC_ACQUIRE));
    put(b, cap, &n, "chams scan: local=%llx/%d callback=%llx/%d enemies=%llu scans=%llu size=%d\n",
        (unsigned long long)visuals::last_local, visuals::last_local_team,
        (unsigned long long)visuals::last_player, visuals::last_team,
        visuals::enemy_ticks, visuals::scan_calls, visuals::scan_size);
    if (!hook_requested() && (vm_camera || visuals::pending_restore() || g_hooked || lu_page_open))
        put(b, cap, &n, "restore pending: camera %d visuals %d hook %d page %d\n",
            vm_camera != 0, visuals::pending_restore(), g_hooked, lu_page_open);
    put(b, cap, &n, "fov %.1f  idx %d  cams %d\n", (double)g_want_fov, g_want_idx, g_nrows);
    put(b, cap, &n, "viewmodel: %s; xyz %.2f %.2f %.2f\n", vm_status,
        (double)g_want_offset.x, (double)g_want_offset.y, (double)g_want_offset.z);
    put(b, cap, &n, "-> %s%s\n", g_target[0] ? g_target : "none", g_target_main ? "  (main!)" : "");
    for (int i = 0; i < g_nrows; i++)
        put(b, cap, &n, "[%d] %s fov %.1f d %.1f%s%s\n", i,
            g_rows[i].name[0] ? g_rows[i].name : "?",
            (double)g_rows[i].fov, (double)g_rows[i].depth,
            g_rows[i].en == 0 ? " off" : "", g_rows[i].ismain ? " main" : "");
    int logged = n;
    put(b, cap, &n, "beat %llu\n", (unsigned long long)vis_now());
    int fd = open(OUT_PATH ".tmp", O_WRONLY | O_CREAT | O_TRUNC, 0666);
    if (fd < 0) {
        static int said;
        if (!said) { said = 1; LG("report open failed: %s errno %d", OUT_PATH, errno); }
    } else {
        ssize_t w = write(fd, b, (size_t)n);
        close(fd);
        if (w == n) {
            if (rename(OUT_PATH ".tmp", OUT_PATH) != 0) LG("report rename failed, errno %d", errno);
        } else LG("report short write: %zd/%d errno %d", w, n, errno);
    }
    // The same text down the channel that cannot be blocked, but only when it has
    // changed - the poll runs every two seconds for the life of the process and the
    // camera list is the same every time. A slider move changes it, which is wanted.
    static unsigned last;
    unsigned h = 2166136261u;
    for (int i = 0; i < logged; i++) h = (h ^ (unsigned char)b[i]) * 16777619u;
    if (h != last) { last = h; b[logged] = 0; LG("%s", b); }
}

/**
 * Retries for the life of the process rather than a fixed number of times: the
 * payload is usually in before the match has loaded, and the assemblies appear
 * whenever they appear. Once hooked it slows to the 2 s poll the cfg needs.
 */
static void* poll_thread(void* a) {
    (void)a;
    LG("payload alive, tid %d", gettid());
    long long last_report = 0, last_camera_retry = 0;
    // The first report must precede every version-specific runtime call.
    write_report();
    for (;;) {
        pthread_mutex_lock(&state_mutex);
        vis_read_cfg();
        clientskins::read_config();
        if (!g_api_ok) { report_stage("resolving IL2CPP"); api_init(); }
        if (now_ms() - last_report >= 1000) {
            read_cfg();
            write_report();
            last_report = now_ms();
        }
        if (g_api_ok && !g_camera_ok && g_core_image && g_want_hook && g_want_fov > 0.f &&
            now_ms() - last_camera_retry >= 2000) {
            last_camera_retry = now_ms();
            bind_unity_methods(g_core_image);
        }
        restore_lu_page();
        if (g_api_ok && !g_hooked && hook_requested()) { resolve_lu(); hook_lu(); }
        // With no outstanding Unity work, a paused game does not need another tick.
        if (g_hooked && !hook_requested() && !vm_camera && !visuals::pending_restore() && !clientskins::pending_restore()) unhook_lu();
        bool hooked = g_hooked;
        pthread_mutex_unlock(&state_mutex);
        usleep(hooked ? 100000 : 500000);
    }
    return nullptr;
}

/**
 * inj holds the process under ptrace while this runs, so it starts a thread and
 * returns immediately - anything slow here stalls the game mid-frame.
 *
 * Two ways in, one body. inj looks for an exported payload_entry and calls it after
 * every .init_array entry has run; the constructor is the fallback for when it does
 * not find one, which is what happened until this symbol existed - the payload was
 * riding on .init_array alone and inj printed "payload_entry not found" every time.
 * Whichever fires first wins and the other is a no-op.
 *
 * The counter only guards this copy of the library. inj maps by hand instead of
 * calling dlopen, so a second injection would be a second copy with its own
 * globals; keeping that from happening is the app's job, and it does it by looking
 * at how old the report is before injecting.
 */
static bool vm_start(const char* how) {
    static int started;
    if (started) return true;
    LG("%s in, pid %d", how, getpid());
    pthread_t t;
    int error = pthread_create(&t, nullptr, poll_thread, nullptr);
    if (error) { LG("pthread_create failed, code %d", error); return false; }
    started = 1;
    pthread_detach(t);
    return true;
}

#ifndef VIEWMODEL_SELF_TEST
extern "C" __attribute__((visibility("default"))) uint64_t payload_entry(void* arg) {
    (void)arg;
    return vm_start("payload_entry") ? PAYLOAD_STARTED : 0;
}

__attribute__((constructor)) static void vm_entry() { vm_start("constructor"); }
#endif
