// Sparkle Drone Gazebo/Ignition Plugin
//
// Bridges an Ignition Gazebo drone model to the Verilated Sparkle SoC
// via POSIX shared memory.
//
// On each simulation step:
//   1. Read IMU, GPS, collision sensors from Gazebo
//   2. Write to shm as sensor data (Q16.16 packed)
//   3. Set sensors_ready = 1, wait for actuators_ready
//   4. Read motor_throttle and pump_duty from shm
//   5. Apply forces to drone model links
//   6. Clear actuators_ready, step physics
//
// Build as an Ignition Gazebo system plugin:
//   - Link: libignition-gazebo6, libignition-plugin1
//   - Install into plugin path, register in world SDF
//
// Usage in SDF:
//   <plugin filename="libsparkle_drone_cosim.so"
//           name="sparkle::drone::CoSimPlugin">
//     <shm_path>/sparkle_drone_cosim</shm_path>
//   </plugin>

#include "cosim_shmem.h"

#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <atomic>
#include <thread>
#include <chrono>
#include <cmath>
#include <cstring>
#include <string>

// Ignition Gazebo headers (uncomment when building against real Gazebo):
// #include <ignition/gazebo/System.hh>
// #include <ignition/gazebo/Model.hh>
// #include <ignition/gazebo/components/Imu.hh>
// #include <ignition/gazebo/components/LinearVelocity.hh>
// #include <ignition/gazebo/components/Pose.hh>
// #include <ignition/gazebo/components/Link.hh>
// #include <ignition/math/Vector3.hh>
// #include <ignition/plugin/Register.hh>

namespace sparkle {
namespace drone {

class CoSimPlugin {
public:
    CoSimPlugin() = default;
    ~CoSimPlugin() {
        if (shm_ptr_) {
            munmap(shm_ptr_, SPARKLE_COSIM_SHM_SIZE);
        }
    }

    // Called on plugin load
    bool Configure(const std::string& shm_path = SPARKLE_COSIM_SHM_PATH) {
        int fd = shm_open(shm_path.c_str(), O_CREAT | O_RDWR, 0666);
        if (fd < 0) return false;
        if (ftruncate(fd, SPARKLE_COSIM_SHM_SIZE) < 0) {
            close(fd);
            return false;
        }
        void* ptr = mmap(nullptr, SPARKLE_COSIM_SHM_SIZE,
                         PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
        close(fd);
        if (ptr == MAP_FAILED) return false;
        shm_ptr_ = (sparkle_cosim_t*)ptr;

        if (shm_ptr_->magic != SPARKLE_COSIM_MAGIC) {
            memset(shm_ptr_, 0, SPARKLE_COSIM_SHM_SIZE);
            shm_ptr_->magic = SPARKLE_COSIM_MAGIC;
            shm_ptr_->version = SPARKLE_COSIM_VERSION;
        }
        return true;
    }

    // Called every physics step (PreUpdate in Ignition)
    // Pseudocode — uncomment Ignition API calls when building.
    void PreUpdate(/* const UpdateInfo& info, EntityComponentManager& ecm */) {
        if (!shm_ptr_) return;

        // ================================================================
        // 1. Read sensors from Gazebo
        // ================================================================
        // auto imu = ecm.Component<components::Imu>(imu_entity_);
        // auto lin_vel = ecm.Component<components::LinearVelocity>(base_link_);
        // auto pose = ecm.Component<components::Pose>(base_link_);

        // Placeholder values (replace with Ignition API reads):
        float accel_x = 0.0f, accel_y = 0.0f, accel_z = -9.81f;
        float gyro_x = 0.0f, gyro_y = 0.0f, gyro_z = 0.0f;
        float lat = 35.6895f, lon = 139.6917f, alt = 100.0f;  // Tokyo
        bool collision = false;

        // ================================================================
        // 2. Pack to shm (Q16.16)
        // ================================================================
        shm_ptr_->accel_x = cosim_f2q(accel_x);
        shm_ptr_->accel_y = cosim_f2q(accel_y);
        shm_ptr_->accel_z = cosim_f2q(accel_z);
        shm_ptr_->gyro_x  = cosim_f2q(gyro_x);
        shm_ptr_->gyro_y  = cosim_f2q(gyro_y);
        shm_ptr_->gyro_z  = cosim_f2q(gyro_z);

        shm_ptr_->gps_lat = (int32_t)(lat * 1e7f);
        shm_ptr_->gps_lon = (int32_t)(lon * 1e7f);
        shm_ptr_->gps_alt = cosim_f2q(alt);
        shm_ptr_->gps_valid = 1;

        shm_ptr_->pressure_alt = cosim_f2q(alt);
        shm_ptr_->battery_voltage = cosim_f2q(12.6f);
        shm_ptr_->battery_low = 0;

        shm_ptr_->collision = collision ? 1 : 0;
        shm_ptr_->obstacle_detected = 0;  // set from vision plugin if any

        for (int i = 0; i < 8; i++) shm_ptr_->rc_ch[i] = 1024;  // center
        shm_ptr_->rc_failsafe = 0;

        // ================================================================
        // 3. Signal sensors ready, wait for actuators
        // ================================================================
        auto flag_ptr = [](uint32_t* p) {
            return reinterpret_cast<std::atomic<uint32_t>*>(p);
        };

        flag_ptr(&shm_ptr_->actuators_ready)->store(0, std::memory_order_release);
        flag_ptr(&shm_ptr_->sensors_ready)->store(1, std::memory_order_release);

        // Wait for Verilator to produce actuators (with timeout)
        auto start = std::chrono::steady_clock::now();
        while (flag_ptr(&shm_ptr_->actuators_ready)->load(std::memory_order_acquire) == 0) {
            auto elapsed = std::chrono::steady_clock::now() - start;
            if (elapsed > std::chrono::milliseconds(100)) {
                // Verilator not responding — freeze or skip
                return;
            }
            std::this_thread::sleep_for(std::chrono::microseconds(10));
        }

        // ================================================================
        // 4. Read actuators and apply to model
        // ================================================================
        float motor_thrust[4];
        for (int m = 0; m < 4; m++) {
            // DShot throttle 48-2047 → thrust 0-max_thrust
            uint16_t t = shm_ptr_->motor_throttle[m];
            float normalized = (float)(t - 48) / 1999.0f;
            if (normalized < 0.0f) normalized = 0.0f;
            if (normalized > 1.0f) normalized = 1.0f;
            motor_thrust[m] = normalized * max_thrust_;
        }

        // Apply forces to rotor links (Ignition API):
        // for (int m = 0; m < 4; m++) {
        //     auto link = ecm.Component<components::Link>(rotor_links_[m]);
        //     math::Vector3d force(0, 0, motor_thrust[m]);
        //     link->AddWorldForce(ecm, force);
        // }

        // Pump duty → spray particle emission rate (if modeled)
        for (int p = 0; p < 4; p++) {
            float duty = (float)shm_ptr_->pump_duty[p] / 65535.0f;
            // emit spray particles at rate proportional to duty
        }
    }

private:
    sparkle_cosim_t* shm_ptr_ = nullptr;
    float max_thrust_ = 10.0f;  // Newtons per motor
};

}  // namespace drone
}  // namespace sparkle

// Ignition plugin registration (uncomment for real build):
// IGNITION_ADD_PLUGIN(sparkle::drone::CoSimPlugin,
//                    ignition::gazebo::System,
//                    ignition::gazebo::ISystemConfigure,
//                    ignition::gazebo::ISystemPreUpdate)
// IGNITION_ADD_PLUGIN_ALIAS(sparkle::drone::CoSimPlugin,
//                           "sparkle::drone::CoSimPlugin")
