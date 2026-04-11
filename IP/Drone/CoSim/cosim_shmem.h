// Sparkle Drone Co-Simulation Shared Memory Interface
//
// Shared memory layout for Ignition Gazebo ↔ Verilator co-simulation.
// Both sides map the same shm region and synchronize via two flags.
//
// Handshake:
//   1. Gazebo writes sensor data, sets sensors_ready = 1, clears actuators_ready
//   2. Verilator spins on sensors_ready, reads sensors, clears sensors_ready
//   3. Verilator runs one SoC tick, writes actuators, sets actuators_ready
//   4. Gazebo spins on actuators_ready, reads actuators, clears actuators_ready
//   5. Gazebo steps physics, loop back to 1
//
// Data formats:
//   - All floats stored as Q16.16 fixed-point int32_t
//   - Conversion: fixed = (int32_t)(float * 65536.0f)
//   - Values:     float = (float)fixed / 65536.0f

#ifndef SPARKLE_COSIM_SHMEM_H
#define SPARKLE_COSIM_SHMEM_H

#include <stdint.h>

#define SPARKLE_COSIM_MAGIC    0x53504B4C  // "SPKL"
#define SPARKLE_COSIM_VERSION  1
#define SPARKLE_COSIM_SHM_PATH "/sparkle_drone_cosim"
#define SPARKLE_COSIM_SHM_SIZE sizeof(sparkle_cosim_t)

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
    // Header
    uint32_t magic;            // = SPARKLE_COSIM_MAGIC
    uint32_t version;          // = SPARKLE_COSIM_VERSION
    uint32_t sensors_ready;    // flag: Gazebo → Verilator
    uint32_t actuators_ready;  // flag: Verilator → Gazebo
    uint64_t cycle_count;      // simulation cycle (for debug)

    // === Sensors (Gazebo → Verilator) ===

    // IMU (all Q16.16)
    int32_t accel_x;           // m/s²
    int32_t accel_y;
    int32_t accel_z;
    int32_t gyro_x;            // rad/s
    int32_t gyro_y;
    int32_t gyro_z;

    // GPS
    int32_t gps_lat;           // 1e-7 degrees
    int32_t gps_lon;
    int32_t gps_alt;           // meters, Q16.16
    uint32_t gps_valid;        // 0 = no fix, 1 = fix

    // Barometer
    int32_t pressure_alt;      // meters, Q16.16

    // Battery
    int32_t battery_voltage;   // volts, Q16.16
    uint32_t battery_low;      // flag

    // RC input (SBUS channels)
    int16_t rc_ch[8];          // raw channel values 172-1811
    uint32_t rc_failsafe;      // flag

    // Obstacle detection (from vision)
    uint32_t obstacle_detected;

    // Collision (from physics)
    uint32_t collision;        // 1 if any contact

    // === Actuators (Verilator → Gazebo) ===

    // Motor throttle (4 motors, DShot range 48-2047)
    uint16_t motor_throttle[4];

    // Pump PWM duty (4 nozzles, 0-65535)
    uint16_t pump_duty[4];

    // Status
    uint32_t failsafe_code;    // 0 = normal, 1-5 = failsafe condition
    uint32_t mission_done;     // 1 if mission complete

    // Reserved for future expansion
    uint32_t reserved[16];
} sparkle_cosim_t;

// Helpers for Q16.16 conversion

static inline int32_t cosim_f2q(float f) {
    return (int32_t)(f * 65536.0f);
}

static inline float cosim_q2f(int32_t q) {
    return (float)q / 65536.0f;
}

#ifdef __cplusplus
}
#endif

#endif // SPARKLE_COSIM_SHMEM_H
