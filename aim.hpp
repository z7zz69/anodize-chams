#pragma once
#include "esp_geometry.hpp"

namespace aim {
struct Angles { float pitch, yaw; };
enum Bone { Head, Neck, Body, Leg };
struct Config {
    bool enabled = false;
    float radius = 3.f, smooth_ms = 260.f;
    int bone = Body;
    bool random = false, spray = false;
    float spray_percent = 70.f;
};
static int selected_bone(const Config& config, uint64_t target, uint32_t cycle) {
    if (!config.random) return config.bone;
    uint64_t x = target ^ (uint64_t(cycle) * 0x9e3779b97f4a7c15ULL);
    x ^= x >> 30; x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27; x *= 0x94d049bb133111ebULL;
    return int((x ^ (x >> 31)) & 3);
}
static uint32_t bone_mask(int bone) {
    switch (bone) {
        case Head: return 1u;
        case Neck: return 1u << 1;
        case Body: return 1u << 3;
        case Leg: return (1u << 15) | (1u << 19);
        default: return 0;
    }
}
static float wrap(float a) { return std::remainder(a, 360.f); }
static bool valid(Angles a) {
    return std::isfinite(a.pitch) && std::isfinite(a.yaw) &&
           std::fabs(a.pitch) <= 90.f && std::fabs(a.yaw) < 100000.f;
}
static bool direction(Vec3 from, Vec3 to, Angles& result) {
    Vec3 d{to.x-from.x,to.y-from.y,to.z-from.z};
    float horizontal=std::hypot(d.x,d.z);
    if (!finite_vec(d) || std::hypot(horizontal,d.y)<.1f) return false;
    constexpr float degrees=57.2957795f;
    result={-std::atan2(d.y,horizontal)*degrees,std::atan2(d.x,d.z)*degrees};
    return valid(result);
}
static float distance(Angles from, Angles to) {
    return std::hypot(to.pitch-from.pitch,wrap(to.yaw-from.yaw));
}
static Angles step(Angles current, Angles wanted, float dt, float smooth_ms) {
    if (!valid(current) || !valid(wanted) || !std::isfinite(dt) || dt<=0 || dt>.1f ||
        !std::isfinite(smooth_ms) || smooth_ms<100 || smooth_ms>600) return current;
    float pitch=wanted.pitch-current.pitch, yaw=wrap(wanted.yaw-current.yaw);
    float length=std::hypot(pitch,yaw);
    if (length<.035f) return current;
    float alpha=1.f-std::exp(-dt*1000.f/smooth_ms);
    alpha=std::min(alpha,30.f*dt/length);
    return {std::clamp(current.pitch+pitch*alpha,-89.f,89.f),wrap(current.yaw+yaw*alpha)};
}
struct Lock {
    uint64_t target=0, since=0, lost=0;
    bool choose(uint64_t candidate, uint64_t now) {
        if (!candidate) { if (target) lost=now; target=0; since=0; return false; }
        if (candidate!=target) {
            if (target) lost=now;
            target=candidate; since=now;
        }
        return now>=since && now-since>=120 && (!lost || now-lost>=220);
    }
};
} // namespace aim
