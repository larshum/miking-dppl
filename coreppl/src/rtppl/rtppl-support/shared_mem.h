/**
 * @file shared_mem.h
 * @author Matthias Becker
 * @brief Wrapper for shared memory communication.
 * @date 2022-09-26
 *
 * @copyright Copyright (c) 2022
 *
 */
#ifndef SHARED_MEM_H_
#define SHARED_MEM_H_

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <semaphore.h>

/**
 * Define this if the functions should print status messages
 */
//#define PRINT_INFO_MSG
#ifdef PRINT_INFO_MSG
  #define SM_PRINT_INFO( fmt, ...) fprintf( stdout, "[SM] " fmt "\r\n", ##__VA_ARGS__)
#else
  #define SM_PRINT_INFO(fmt, ...)
#endif

/**
 * Define this if the functions should print error messages
 */
#define PRINT_ERROR_MSG
#ifdef PRINT_ERROR_MSG
  #define SM_PRINT_ERROR( fmt, ...) fprintf( stdout, "[SM ERROR]" fmt " [%s:%d]\r\n", ##__VA_ARGS__, __FUNCTION__, __LINE__)
#else
  #define SM_PRINT_ERROR( fmt, ...)
#endif

/**
 * Return values used
 */
#define SM_OK     0
#define SM_ERROR  1

/**
 * Type to represent all required management parts for a shared memory object.
 */
typedef struct {
  char* smName;           // shared memory name
  char* mutexName;        // mutex name
  sem_t* mutex;           // mutex
  int fd_sm;              // fd

} sm_mgmt_t;

/**
 * Type to represent one shared memory unit
 */
typedef struct {
  char*       name;       // name of the shared memory object
  uint32_t    size;       // size of the shared memory object
  void*       data_p;     // pointer to the data
  sm_mgmt_t*  mgmt;       // management for shared memory and mutex
} shared_mem_t;

/** Infrastructure Functions **************************************************/

/**
 * Function is called once to initialize the shared memory structures and
 * mutexes. That way there is no dependency between creator and user of
 * mutex / shared memory.
 */
uint8_t sm_platform_setup();

/**
 * Function called to cleanup all shared memory infrastructure when the ES-char
 * application terminates.
 */
uint8_t sm_platform_teardown();

/** User Functions ************************************************************/

/**
 * Open the shared memory object and map it to the process address space.
 * If the shared memory object does not exist jet it is created.
 */
uint8_t sm_open(shared_mem_t* sm);

/**
 * Open all shared memory objects
 */
uint8_t sm_open_all(void);

/**
 * Copies the content of the shred memory object to out_data
 */
uint8_t sm_read(shared_mem_t* sm, void* out_data);

/**
 * Copies the data at in_data to the shared memory object
 */
uint8_t sm_write(shared_mem_t* sm, void* in_data);

#endif //SHARED_MEM_H_
