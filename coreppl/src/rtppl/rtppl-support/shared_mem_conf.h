/**
 * @file shared_mem_conf.h
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

#ifndef SHARED_MEM_CONF_H_
#define SHARED_MEM_CONF_H_

/**
 * Type to represent one sensor value sample
 */
typedef struct{
  long long ts;   // timestamp of this data value in ms
  double val;  // value of the sensor (unit depends on sensor)
} sensor_val_t;

/**
 * Configuration for each registered shared memory object (in shared_mem_conf.c)
 */
extern shared_mem_t sm_regs[];

/**
 * Shortcut to reach the right element of the configuration for each
 * shared memory object.
 */
#define DISTANCE_FRONT_LEFT   (&sm_regs[0])
#define DISTANCE_FRONT_RIGHT  (&sm_regs[1])
#define DISTANCE_BACK_LEFT    (&sm_regs[2])
#define DISTANCE_BACK_RIGHT   (&sm_regs[3])
#define DISTANCE_SIDE_LEFT    (&sm_regs[4])
#define DISTANCE_SIDE_RIGHT   (&sm_regs[5])
#define SPEED_VAL_LEFT        (&sm_regs[6])
#define SPEED_VAL_RIGHT       (&sm_regs[7])
#define STEERING_ANGLE        (&sm_regs[8])
#define START_TIME	          (&sm_regs[9])
#define TRUE_X_COORD          (&sm_regs[10])
#define TRUE_Y_COORD          (&sm_regs[11])
#define TRUE_DIRECTION        (&sm_regs[12])
#define OBS_POSITION          (&sm_regs[13])


/**
 * Number of shared memory objects configured.
 */
#define SM_OBJECT_COUNT 14

#endif //SHARED_MEM_CONF_H_
