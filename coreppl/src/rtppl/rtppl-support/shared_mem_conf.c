/**
 * @file shared_mem_conf.c
 * @author Matthias Becker
 * @brief Wrapper for shared memory communication.
 * @date 2022-09-27
 *
 * @copyright Copyright (c) 2022
 *
 */

/*******************************************************************************
  THE CONTENT OF THIS FILE SHOULD BE GENERATED.
*******************************************************************************/

#include "shared_mem.h"
#include "shared_mem_conf.h"

/**
 * All signals shared on the node.
 */
shared_mem_t sm_regs[] = {
  {
    .name = "DistanceFrontLeft",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "DistanceFrontRight",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "DistanceBackLeft",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "DistanceBackRight",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "DistanceSideLeft",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "DistanceSideRight",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "SpeedWheelLeft",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "SpeedWheelRight",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "SteeringAngle",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "StartTime",
    .size = sizeof(sensor_val_t),
    .mgmt  = NULL
  },{
    .name = "TrueXCoord",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "TrueYCoord",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "TrueDirection",
    .size = sizeof(sensor_val_t),
    .mgmt = NULL
  },{
    .name = "ObservedPosition",
    .size = 1 << 16,
    .mgmt = NULL
  }
};
