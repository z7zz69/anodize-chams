#pragma once
#include "esp_geometry.hpp"
#include <algorithm>

// Bone-attached collision geometry, projected by the external ESP worker.
// Layout confirmed against the reference APK; no Unity shader or callback needed.
namespace chams {
struct Quat { float x, y, z, w; };
struct Transform { Vec3 position; float pad0; Quat rotation; Vec3 scale; float pad1; };
static_assert(sizeof(Transform)==48, "Unity transform array stride");
struct Pose { Vec3 position; Quat rotation; Vec3 scale; bool valid; };
struct Shape { int bone, capsule; Vec3 center, size; int axis; };
static constexpr int BONE_COUNT = 22;
static constexpr int BONE_OFFSETS[BONE_COUNT] = {
    0x20,0x28,-1,0x30,0x38,0x48,0x50,0x58,0x60,0x68,0x70,
    0x78,0x80,0x88,0x90,0x98,0xa0,0xa8,0xb0,0xb8,0xc0,0xc8
};
static constexpr Shape SHAPES[] = {
    {0,1,{0,.1f,0},{.115f,.23f,.115f},1},
    {1,1,{0,.056f,-.023f},{.0776f,.1934f,.0776f},1},
    {3,0,{0,-.01f,.0014f},{.3254f,.1884f,.2497f},0},
    {4,0,{0,.1167f,.0013f},{.3654f,.2567f,.2315f},0},
    {5,1,{-.0933f,-.0125f,0},{.0926f,.2486f,.0926f},0},
    {6,1,{-.142f,0,0},{.07f,.3124f,.07f},0},
    {7,1,{-.1141f,0,0},{.06f,.346f,.06f},0},
    {8,0,{-.0466f,-.014f,-.009f},{.1511f,.0798f,.0994f},0},
    {9,1,{.0933f,.0162f,0},{.0926f,.2486f,.0926f},0},
    {10,1,{.1141f,0,-.0001f},{.06f,.346f,.06f},0},
    {11,1,{.142f,0,0},{.07f,.3124f,.07f},0},
    {12,0,{.0466f,.0186f,.009f},{.1511f,.0798f,.0994f},0},
    {13,0,{0,0,.0002f},{.339f,.1367f,.2543f},0},
    {14,1,{-.2156f,.0067f,.0103f},{.098f,.5744f,.098f},0},
    {15,1,{-.2059f,-.0079f,0},{.083f,.576f,.083f},0},
    {17,0,{.0419f,.0227f,-.0019f},{.2887f,.0876f,.1218f},0},
    {18,1,{.2156f,.0067f,-.0103f},{.098f,.5744f,.098f},0},
    {19,1,{.2059f,-.0079f,0},{.083f,.576f,.083f},0},
    {21,0,{-.0374f,-.0299f,.0025f},{.2887f,.0876f,.1218f},0}
};
static Vec3 add(Vec3 a, Vec3 b) { return {a.x+b.x,a.y+b.y,a.z+b.z}; }
static Vec3 mul(Vec3 a, Vec3 b) { return {a.x*b.x,a.y*b.y,a.z*b.z}; }
static Vec3 cross(Vec3 a, Vec3 b) {
    return {a.y*b.z-a.z*b.y,a.z*b.x-a.x*b.z,a.x*b.y-a.y*b.x};
}
static Vec3 rotate(Quat q, Vec3 v) {
    Vec3 u{q.x,q.y,q.z}, t = cross(u,v);
    t = {2*t.x,2*t.y,2*t.z};
    return add(v,add({q.w*t.x,q.w*t.y,q.w*t.z},cross(u,t)));
}
static Quat multiply(Quat a, Quat b) {
    return {a.w*b.x+a.x*b.w+a.y*b.z-a.z*b.y,
            a.w*b.y-a.x*b.z+a.y*b.w+a.z*b.x,
            a.w*b.z+a.x*b.y-a.y*b.x+a.z*b.w,
            a.w*b.w-a.x*b.x-a.y*b.y-a.z*b.z};
}
static bool valid_rotation(Quat q) {
    float n=q.x*q.x+q.y*q.y+q.z*q.z+q.w*q.w;
    return std::isfinite(n) && n>.9f && n<1.1f;
}
static bool valid_transform(const Transform& t) {
    return finite_vec(t.position) && finite_vec(t.scale) && valid_rotation(t.rotation) &&
        std::fabs(t.position.x)<20000 && std::fabs(t.position.y)<20000 && std::fabs(t.position.z)<20000 &&
        std::fabs(t.scale.x)>.0001f && std::fabs(t.scale.y)>.0001f && std::fabs(t.scale.z)>.0001f &&
        std::fabs(t.scale.x)<100 && std::fabs(t.scale.y)<100 && std::fabs(t.scale.z)<100;
}
static bool pointer(uint64_t p) { return p>0x10000 && p<0x0000ffffffffffffull; }
struct Buffers { uint64_t matrices, parents; };
struct CachePage {
    Buffers buffers;
    int start, count;
    Transform transforms[16];
    int parents[16];
};
struct Cache {
    CachePage pages[32]; int count = 0;
    uint64_t hierarchy = 0; Buffers buffers{};
};

template<class Read> static bool cached_transform(Buffers buffers, int index, Transform& transform,
                                                  int& parent, Cache& cache, const Read& read) {
    CachePage* page=nullptr;
    for (int i=0;i<cache.count;i++) {
        auto& p=cache.pages[i];
        if (p.buffers.matrices==buffers.matrices && p.buffers.parents==buffers.parents &&
            index>=p.start && index<p.start+p.count) { page=&p; break; }
    }
    if (!page) {
        if (cache.count==32) return false;
        auto& p=cache.pages[cache.count];
        p.buffers=buffers; p.start=index&~15; p.count=16;
        // Read nearby joints together. At an unreadable allocation boundary,
        // retry just the requested joint instead of dropping the entire rig.
        if (!read(buffers.matrices+uint64_t(p.start)*48,p.transforms,sizeof p.transforms) ||
            !read(buffers.parents+uint64_t(p.start)*4,p.parents,sizeof p.parents)) {
            p.start=index; p.count=1;
            if (!read(buffers.matrices+uint64_t(index)*48,p.transforms,sizeof(Transform)) ||
                !read(buffers.parents+uint64_t(index)*4,p.parents,sizeof(int))) return false;
        }
        cache.count++; page=&p;
    }
    transform=page->transforms[index-page->start];
    parent=page->parents[index-page->start];
    return valid_transform(transform) && parent>=-1;
}

template<class Read> static bool read_pose(uint64_t managed, Pose& out, Cache& cache, const Read& read) {
    out.valid = false;
    uint64_t native = 0;
    struct { uint64_t hierarchy; int index, pad; } access{};
    if (!pointer(managed) || !read(managed+0x10,&native,8) || !pointer(native) ||
        !read(native+0x28,&access,sizeof access) || !pointer(access.hierarchy) ||
        access.index<0 || access.index>100000) return false;
    if (cache.hierarchy!=access.hierarchy) {
        Buffers buffers{};
        if (!read(access.hierarchy+0x18,&buffers,sizeof buffers) ||
            !pointer(buffers.matrices) || !pointer(buffers.parents)) return false;
        cache.hierarchy=access.hierarchy; cache.buffers=buffers;
    }
    out.position={0,0,0}; out.rotation={0,0,0,1}; out.scale={1,1,1};
    int index=access.index;
    // One snapshot per player: shared ancestors are read once; no cross-frame cache.
    for (int depth=0; index>=0 && depth<128; depth++) {
        if (index>100000) return false;
        Transform t; int parent;
        if (!cached_transform(cache.buffers,index,t,parent,cache,read)) return false;
        out.position=add(t.position,rotate(t.rotation,mul(t.scale,out.position)));
        out.rotation=multiply(t.rotation,out.rotation);
        out.scale=mul(t.scale,out.scale);
        index=parent;
    }
    out.valid=index==-1 && finite_vec(out.position) && valid_rotation(out.rotation) && finite_vec(out.scale);
    return out.valid;
}

template<class Read> static int read_rig(uint64_t player, Vec3 feet, Pose (&pose)[BONE_COUNT], const Read& read,
                                        uint32_t mask = UINT32_MAX) {
    uint64_t view=0, rig=0, slots[22]{};
    for (auto& p:pose) p.valid=false;
    if (!pointer(player) || !finite_vec(feet) || !read(player+0x48,&view,8) || !pointer(view) || !read(view+0x48,&rig,8) ||
        !pointer(rig) || !read(rig+0x20,slots,sizeof slots)) return 0;
    Cache cache{};
    int found=0;
    for (int i=0;i<BONE_COUNT;i++) if (BONE_OFFSETS[i]>=0 && (mask & (1u << i))) {
        auto& p=pose[i];
        if (!read_pose(slots[(BONE_OFFSETS[i]-0x20)/8],p,cache,read)) continue;
        Vec3 d{p.position.x-feet.x,p.position.y-feet.y,p.position.z-feet.z};
        p.valid=d.x*d.x+d.y*d.y+d.z*d.z<16.f;
        if (p.valid) found++;
    }
    if (pose[17].valid && pose[21].valid) {
        Vec3 center{(pose[17].position.x+pose[21].position.x)*.5f,
            std::min(pose[17].position.y,pose[21].position.y),
            (pose[17].position.z+pose[21].position.z)*.5f};
        float dx=center.x-feet.x, dz=center.z-feet.z;
        // Animation culling can leave a coherent skeleton at an old location.
        // Use the current-position fallback rather than drawing that stale body.
        if (dx*dx+dz*dz>.64f || std::fabs(center.y-feet.y)>.85f) {
            for (auto& p:pose) p.valid=false;
            return 0;
        }
    }
    return found;
}

static float turn(Point2 a, Point2 b, Point2 c) {
    return (b.x-a.x)*(c.y-a.y)-(b.y-a.y)*(c.x-a.x);
}
static int clip_polygon(Point2* polygon, int n) {
    Point2 clipped[2*MAX_PROJECTED];
    for (int plane=0;plane<4 && n;plane++) {
        auto distance=[plane](Point2 p) {
            float v=plane<2 ? p.x : p.y;
            return (plane&1) ? 2.f-v : v+1.f;
        };
        int count=0;
        Point2 a=polygon[n-1]; float da=distance(a);
        for (int i=0;i<n;i++) {
            Point2 b=polygon[i]; float db=distance(b);
            if ((da<0)!=(db<0)) {
                float t=da/(da-db);
                clipped[count++]={a.x+(b.x-a.x)*t,a.y+(b.y-a.y)*t};
            }
            if (db>=0) clipped[count++]=b;
            a=b; da=db;
        }
        n=count;
        std::copy(clipped,clipped+n,polygon);
    }
    return n;
}
static bool part(const Shape& shape, const Pose& pose, const float matrix[16], ChamsPart& out) {
    out.count=0;
    if (!pose.valid || !valid_rotation(pose.rotation)) return false;
    Vec3 cloud[MAX_CLOUD]; int n=0;
    if (!shape.capsule) {
        for (int i=0;i<8;i++) cloud[n++]={shape.size.x*((i&1)?.5f:-.5f),
            shape.size.y*((i&2)?.5f:-.5f),shape.size.z*((i&4)?.5f:-.5f)};
    } else {
        float radius=shape.size.x, half=std::max(0.f,shape.size.y*.5f-radius);
        for (int side=-1;side<=1;side+=2) {
            float tip[3]{}; tip[shape.axis]=side*(half+radius);
            cloud[n++]={tip[0],tip[1],tip[2]};
            for (int j=0;j<8;j++) {
                float v[3]{}; v[shape.axis]=side*half;
                static constexpr float circle[8][2]={{1,0},{.70710678f,.70710678f},{0,1},
                    {-.70710678f,.70710678f},{-1,0},{-.70710678f,-.70710678f},{0,-1},{.70710678f,-.70710678f}};
                v[(shape.axis+1)%3]=radius*circle[j][0];
                v[(shape.axis+2)%3]=radius*circle[j][1];
                cloud[n++]={v[0],v[1],v[2]};
            }
        }
    }
    Point2 points[MAX_PROJECTED], hull[2*MAX_PROJECTED];
    for (int i=0;i<n;i++) {
        cloud[i]=add(pose.position,rotate(pose.rotation,mul(pose.scale,add(shape.center,cloud[i]))));
        if (!finite_vec(cloud[i])) return false;
    }
    n=project_cloud(cloud,n,matrix,points);
    if (n<3) return false;
    std::sort(points,points+n,[](Point2 a,Point2 b){return a.x<b.x || (a.x==b.x && a.y<b.y);});
    int k=0;
    for (int i=0;i<n;i++) {
        while (k>=2 && turn(hull[k-2],hull[k-1],points[i])<=0) k--;
        hull[k++]=points[i];
    }
    for (int i=n-2, limit=k+1;i>=0;i--) {
        while (k>=limit && turn(hull[k-2],hull[k-1],points[i])<=0) k--;
        hull[k++]=points[i];
    }
    k=clip_polygon(hull,k-1);
    if (k<3) return false;
    out.count=std::min(k,MAX_CHAMS_POINTS);
    for (uint32_t i=0;i<out.count;i++) out.points[i]=hull[i*k/out.count];
    return true;
}

static void build(const Pose (&pose)[BONE_COUNT], const float matrix[16], uint32_t flags, EspPlayer& out) {
    if (flags&ESP_CHAMS) for (const auto& shape:SHAPES) {
        if (out.part_count==MAX_CHAMS_PARTS) break;
        if (part(shape,pose[shape.bone],matrix,out.parts[out.part_count])) out.part_count++;
    }
    static constexpr int links[][2]={{0,1},{1,4},{4,3},{3,13},{4,5},{5,6},{6,7},{7,8},
        {4,9},{9,11},{11,10},{10,12},{13,14},{14,15},{15,17},{13,18},{18,19},{19,21}};
    if (flags&ESP_SKELETON) for (const auto& link:links) {
        if (!pose[link[0]].valid || !pose[link[1]].valid) continue;
        Segment s;
        if (project_segment(pose[link[0]].position,pose[link[1]].position,matrix,s))
            out.segments[out.segment_count++]=s;
    }
}

// Culled/LOD models may have missing or stale bone transforms. This deliberately
// approximate body volume follows the current movement position, never old bones.
static void fallback(Vec3 feet, const float matrix[16], EspPlayer& out) {
    if (out.part_count) return;
    // A neutral six-part body instead of a pointed capsule. Face its width
    // toward the camera so a side view does not collapse it into a thin line.
    float yaw=-std::atan2(matrix[8],matrix[0]);
    const Pose pose{feet,{0,std::sin(yaw*.5f),0,std::cos(yaw*.5f)},{1,1,1},true};
    static constexpr Shape body[] = {
        {0,0,{0,1.555f,0},{.22f,.25f,.22f},0},
        {0,0,{0,1.105f,0},{.38f,.65f,.24f},0},
        {0,0,{-.26f,1.075f,0},{.14f,.6f,.16f},0},
        {0,0,{ .26f,1.075f,0},{.14f,.6f,.16f},0},
        {0,0,{-.105f,.4f,0},{.17f,.8f,.18f},0},
        {0,0,{ .105f,.4f,0},{.17f,.8f,.18f},0}
    };
    for (const auto& shape:body)
        if (part(shape,pose,matrix,out.parts[out.part_count])) out.part_count++;
}
} // namespace chams
