#pragma once
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif

#include <stdbool.h>
#include "types.h"

#if defined(_WIN32) || defined(_WIN64)
#define VALK_PLATFORM_WINDOWS 1
#else
#define VALK_PLATFORM_POSIX 1
#include <pthread.h>
#endif

#ifdef VALK_PLATFORM_POSIX
typedef pthread_t valk_thread_t;
typedef pthread_mutex_t valk_mutex_t;
typedef pthread_cond_t valk_cond_t;
typedef pthread_attr_t valk_thread_attr_t;
#else
typedef void* valk_thread_t;
typedef void* valk_mutex_t;
typedef void* valk_cond_t;
typedef void* valk_thread_attr_t;
#endif

typedef void* (*valk_thread_fn)(void*);

int valk_mutex_init(valk_mutex_t* mutex);
int valk_mutex_destroy(valk_mutex_t* mutex);
int valk_mutex_lock(valk_mutex_t* mutex);
int valk_mutex_unlock(valk_mutex_t* mutex);

int valk_cond_init(valk_cond_t* cond);
int valk_cond_destroy(valk_cond_t* cond);
int valk_cond_signal(valk_cond_t* cond);
int valk_cond_broadcast(valk_cond_t* cond);
int valk_cond_wait(valk_cond_t* cond, valk_mutex_t* mutex);
int valk_cond_timedwait(valk_cond_t* cond, valk_mutex_t* mutex, u32 timeout_ms);

int valk_thread_create(valk_thread_t* thread, valk_thread_attr_t* attr,
                       valk_thread_fn fn, void* arg);
int valk_thread_join(valk_thread_t thread, void** retval);
valk_thread_t valk_thread_self(void);
bool valk_thread_equal(valk_thread_t a, valk_thread_t b);
int valk_thread_setname(valk_thread_t thread, const char* name);
int valk_thread_getname(valk_thread_t thread, char* buf, u64 len);

int valk_thread_attr_init(valk_thread_attr_t* attr);
int valk_thread_attr_setdetached(valk_thread_attr_t* attr, bool detached);
