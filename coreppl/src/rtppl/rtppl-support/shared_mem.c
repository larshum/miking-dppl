/**
 * @file shared_mem.c
 * @author Matthias Becker
 * @brief Wrapper for shared memory communication.
 * @date 2022-09-26
 *
 * @copyright Copyright (c) 2022
 *
 */

#include "shared_mem.h"
#include "shared_mem_conf.h"
#include <errno.h>

/** Private Defines ***********************************************************/

#define SM_STRING  "_sm"
#define MUTEX_STRING  "_mutex"

/** Private Function Prototyp[es **********************************************/

/**
 * Initialize the shared memory object for a user process
 */
uint8_t sm_local_init(shared_mem_t* sm);

/** Infrastructure Functions **************************************************/

/**
 * Function is called once to initialize the shared memory structures and
 * mutexes. That way there is no dependency between creator and user of
 * mutex / shared memory.
 */
uint8_t sm_platform_setup() {

  // Prepare each shared memory object so the user processes can use it.
  for (int i = 0; i < SM_OBJECT_COUNT; i++) {

    sm_local_init(&sm_regs[i]);

    // open the mutex as a writer (create it as well)
    char* mutex_name = (&sm_regs[i])->mgmt->mutexName;
    if ((sm_regs[i].mgmt->mutex = sem_open(mutex_name, O_CREAT, 0660, 0)) == SEM_FAILED) {
      SM_PRINT_ERROR("Error creating the mutex %s", mutex_name);
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Successfully created mutex %s!", mutex_name);
    }

    // Open the shared memory
    char* sm_name = (&sm_regs[i])->mgmt->smName;
    if ((sm_regs[i].mgmt->fd_sm = shm_open (sm_name, O_RDWR | O_CREAT | O_EXCL, 0660)) == -1) {
      SM_PRINT_ERROR("Could not open shared memory %s -> %s", sm_name, strerror(errno));
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Successfully created shared memory %s!", sm_name);
    }

    // Configure the size of the shared memory
    if (ftruncate (sm_regs[i].mgmt->fd_sm, sm_regs[i].size) == -1) {
       SM_PRINT_ERROR ("Could not configure size of shared memory %s", sm_name);
       return SM_ERROR;
     }

    // Map the shared memory to the address space of the program
    if ((sm_regs[i].data_p = mmap (NULL, sm_regs[i].size, PROT_READ | PROT_WRITE, MAP_SHARED,
            sm_regs[i].mgmt->fd_sm, 0)) == MAP_FAILED) {
      SM_PRINT_ERROR("Could not map the shared memory %s", sm_name);
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Successfully mapped shared memory %s!", sm_name);
    }

    // All done, we can post the mutex to allow others to use the shared memory object
    if (sem_post (sm_regs[i].mgmt->mutex) == -1) {
        SM_PRINT_ERROR ("Could not post mutex %s", mutex_name);
        return SM_ERROR;
      } else {
        SM_PRINT_INFO("Completed configuration for shared memory %s", sm_regs[i].name);
      }
  }

  return SM_OK;
}

/**
 * Function called to cleanup all shared memory infrastructure when the ES-char
 * application terminates.
 */
uint8_t sm_platform_teardown() {

  // Remove all shared memory objects
  for (int i = 0; i < SM_OBJECT_COUNT; i++) {
    if (shm_unlink(sm_regs[i].mgmt->smName) == -1) {
      SM_PRINT_ERROR("Could not unlink shared memory %s -> %s", sm_regs[i].mgmt->smName, strerror(errno));
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Unlinked shared memory %s", sm_regs[i].mgmt->smName);
    }
  }

  return SM_OK;
}

/** User Functions ************************************************************/

/**
 * Open the shared memory object and map it to the process address space.
 * If the shared memory object does not exist jet it is created.
 */
uint8_t sm_open(shared_mem_t* sm) {

  if (sm->mgmt == NULL) {

    // Initialize the management structure
    if (sm_local_init(sm) != SM_OK) {
      return SM_ERROR;
    }

    char* mutex_name = sm->mgmt->mutexName;

    //open the mutex
    if ((sm->mgmt->mutex = sem_open(mutex_name, 0, 0, 0)) == SEM_FAILED) {
      SM_PRINT_ERROR("opening the mutex %s.", mutex_name);
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Opened mutex %s", mutex_name);
    }

    //open the shared memory
    char* sm_name = sm->mgmt->smName;
    if ((sm->mgmt->fd_sm = shm_open (sm_name, O_RDWR, 0)) == -1) {
      SM_PRINT_ERROR("Could not open the shared memory %s -> %s", sm_name, strerror(errno));
      return SM_ERROR;
    } else {
      SM_PRINT_INFO("Opened shared memory %s", sm_name);
    }

    // Map the shared memory to the address space of the program
    if ((sm->data_p = mmap (NULL, sm->size, PROT_READ | PROT_WRITE, MAP_SHARED,
            sm->mgmt->fd_sm, 0)) == MAP_FAILED) {
        SM_PRINT_ERROR("Could not map the shared memory %s -> %s", sm_name, strerror(errno));
        return SM_ERROR;
    } else {
      SM_PRINT_INFO("Successfully mapped shared memory %s!", sm_name);
    }
  }

  return SM_OK;
}


/**
 * Open all shared memory objects
 */
uint8_t sm_open_all(void) {

  for (int i = 0; i < SM_OBJECT_COUNT; i++) {
    if (sm_open(&sm_regs[i]) != SM_OK) {
      return SM_ERROR;
    }
  }

  return SM_OK;
}
/**
 * Copies the content of the shred memory object to out_data
 */
uint8_t sm_read(shared_mem_t* sm, void* out_data) {

  // Take the mutex
  if (sem_wait(sm->mgmt->mutex) == -1) {
    SM_PRINT_ERROR("waiting for mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    return SM_ERROR;
  } else {
    SM_PRINT_INFO("Successfully took mutex %s!", sm->mgmt->mutexName);
  }

  // Copy the content from the shared memory
  memcpy(out_data, sm->data_p, sm->size);

  // Give the mutex back
  if (sem_post(sm->mgmt->mutex) == -1) {
    SM_PRINT_ERROR("returning mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    return SM_ERROR;
  } else {
    SM_PRINT_INFO("Successfully returned mutex %s!", sm->mgmt->mutexName);
  }

  return SM_OK;
}

/**
 * Copies the data at in_data to the shared memory object
 */
uint8_t sm_write(shared_mem_t* sm, void* in_data) {

  // Take the mutex
  if (sem_wait(sm->mgmt->mutex) == -1) {
    SM_PRINT_ERROR("waiting for mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    return SM_ERROR;
  } else {
    SM_PRINT_INFO("Successfully took mutex %s!", sm->mgmt->mutexName);
  }

  // Copy the content to the shared memory
  memcpy(sm->data_p, in_data, sm->size);

  // Give the mutex back
  if (sem_post(sm->mgmt->mutex) == -1) {
    SM_PRINT_ERROR("returning mutex %s -> %s", sm->mgmt->mutexName, strerror(errno));
    return SM_ERROR;
  } else {
    SM_PRINT_INFO("Successfully returned mutex %s!", sm->mgmt->mutexName);
  }

  return SM_OK;
}

/** Private Helper Functions **************************************************/

/**
 * Initialize the shared memory object for a user process
 */
uint8_t sm_local_init(shared_mem_t* sm) {

  sm->mgmt = (sm_mgmt_t*)malloc(sizeof(sm_mgmt_t));

  //copy the name
  sm->mgmt->smName = (char*)malloc(strlen(sm->name) + strlen(SM_STRING) + 1);
  sprintf(sm->mgmt->smName, "%s%s", sm->name, SM_STRING);

  //create the mutex name
  sm->mgmt->mutexName = (char*)malloc(strlen(sm->name) + strlen(MUTEX_STRING) + 1);
  sprintf(sm->mgmt->mutexName, "%s%s", sm->name, MUTEX_STRING);


  SM_PRINT_INFO("Initialized Management Structure -> SM Name: %s Mutex Name: %s", sm->mgmt->smName, sm->mgmt->mutexName);

  return SM_OK;
}
