/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */
/* 이 파일은 교육용 운영체제 Nachos의 소스 코드를 기반으로 작성되었습니다.
   Nachos 저작권 고지를 아래에 전문 그대로 실었습니다. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
   */
/* 저작권 (c) 1992-1996 캘리포니아 대학교 이사회.
   모든 권리 보유.

   본 소프트웨어와 그 문서를 어떠한 목적을 위해서든 무료로,
   별도의 서면 합의 없이 사용·복제·수정·배포할 수 있도록 허가합니다.
   단, 위의 저작권 고지와 다음 두 단락이 이 소프트웨어의 모든 사본에
   반드시 포함되어야 합니다.

   어떠한 경우에도 캘리포니아 대학교는 본 소프트웨어 및 문서의 사용에서
   발생하는 직접적·간접적·특별·부수적·결과적 손해에 대해 책임을 지지
   않습니다. 이는 캘리포니아 대학교가 그러한 손해 가능성에 대해 사전에
   통지받았더라도 마찬가지입니다.

   캘리포니아 대학교는 상품성 또는 특정 목적에의 적합성에 대한 묵시적
   보증을 포함하되 이에 국한되지 않는 모든 보증을 명시적으로 부인합니다.
   본 소프트웨어는 “있는 그대로(AS IS)” 제공되며, 캘리포니아 대학교는
   유지보수, 지원, 업데이트, 기능 개선 또는 수정에 대한 어떤 의무도
   부담하지 않습니다.
   */

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"


/* 프로토 타입 */
static bool prio_greater (const struct list_elem *a,
                          const struct list_elem *b,
                          void *aux UNUSED);
static bool greater_waiter (const struct list_elem *a,
                            const struct list_elem *b,
                            void *aux UNUSED);
static bool prio_less (const struct list_elem *a,
                       const struct list_elem *b,
                       void *aux UNUSED);


/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
   decrement it.

   - up or "V": increment the value (and wake up one waiting
   thread, if any). */
   
/* 세마포어 SEMA를 VALUE 값으로 초기화한다. 세마포어는 0 이상의 정수와
   이를 조작하는 두 가지 원자적 연산으로 이루어진다.

   - down 또는 "P": 값이 양수가 될 때까지 기다린 뒤, 값을 1 감소시킨다.

   - up 또는 "V": 값을 1 증가시킨다(그리고 대기 중인 스레드가 있으면 하나를 깨운다). */
void
sema_init (struct semaphore *sema, unsigned value) {
	ASSERT (sema != NULL);

	sema->value = value;
	list_init (&sema->waiters);
}

/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. This is
   sema_down function. */

static bool prio_greater(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED) {
	const struct thread *ta = list_entry(a, struct thread, elem);
    const struct thread *tb = list_entry(b, struct thread, elem);
	return ta->priority > tb->priority;
}
static bool prio_less (const struct list_elem *a,
                       const struct list_elem *b,
                       void *aux UNUSED) {
  const struct thread *ta = list_entry (a, struct thread, elem);
  const struct thread *tb = list_entry (b, struct thread, elem);
  return ta->priority < tb->priority;  // !!! less
}


/* 세마포어에 대한 down 또는 "P" 연산. SEMA의 값이 양수가 될 때까지 기다린 뒤
   원자적으로 값을 1 감소시킨다.

   이 함수는 수면(sleep)할 수 있으므로 인터럽트 핸들러 내에서 호출하면 안 된다.
   인터럽트를 비활성화한 상태에서 호출할 수는 있지만, 수면에 들어가면
   다음에 스케줄되는 스레드가 인터럽트를 다시 켜게 될 것이다.
   이 함수는 sema_down이다. */
void
sema_down (struct semaphore *sema) {
	enum intr_level old_level;

	ASSERT (sema != NULL);
	ASSERT (!intr_context ());

	old_level = intr_disable ();
	while (sema->value == 0) {
		list_insert_ordered (
			&sema->waiters,
			&thread_current ()->elem,
			prio_greater,
			NULL
		);
		thread_block ();
	}
	sema->value--;
	intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */

/* 세마포어의 값이 0이 아닐 때에만 수행하는 down 또는 "P" 연산.
   값을 감소시켰다면 true를, 그렇지 않으면 false를 반환한다.

   이 함수는 인터럽트 핸들러에서 호출할 수 있다. */
bool
sema_try_down (struct semaphore *sema) {
	enum intr_level old_level;
	bool success;

	ASSERT (sema != NULL);

	old_level = intr_disable ();
	if (sema->value > 0)
	{
		sema->value--;
		success = true;
	}
	else
		success = false;
	intr_set_level (old_level);

	return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */

/* 세마포어에 대한 up 또는 "V" 연산. SEMA의 값을 1 증가시키고,
   대기 중인 스레드가 있으면 그중 하나를 깨운다.

   이 함수는 인터럽트 핸들러에서 호출할 수 있다. */
void
sema_up (struct semaphore *sema) {
	enum intr_level old_level;
	struct thread * cur   = thread_current();
	struct thread * woken = NULL;

	ASSERT (sema != NULL);

	old_level = intr_disable ();
	sema->value++;
   if (!list_empty (&sema->waiters)) {
      list_sort (&sema->waiters, prio_greater, NULL);
      struct list_elem *e = list_pop_front (&sema->waiters);
      woken = list_entry (e, struct thread, elem);
      thread_unblock (woken);
   }
      intr_set_level (old_level);
   if (woken && woken->priority > cur->priority) {
      if (intr_context()) intr_yield_on_return();
      else                thread_yield();
   }
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */

/* 두 개의 스레드 사이에서 제어가 "핑퐁"처럼 오가게 하여
   세마포어를 자가 테스트한다. 동작을 확인하려면 printf() 호출을
   삽입하여 출력해 보라. */
void
sema_self_test (void) {
	struct semaphore sema[2];
	int i;

	printf ("Testing semaphores...");
	sema_init (&sema[0], 0);
	sema_init (&sema[1], 0);
	thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
	for (i = 0; i < 10; i++)
	{
		sema_up (&sema[0]);
		sema_down (&sema[1]);
	}
	printf ("done.\n");
}

/* Thread function used by sema_self_test(). */

/* sema_self_test()에서 사용하는 스레드 함수. */
static void
sema_test_helper (void *sema_) {
	struct semaphore *sema = sema_;
	int i;

	for (i = 0; i < 10; i++)
	{
		sema_down (&sema[0]);
		sema_up (&sema[1]);
	}
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */

/* LOCK을 초기화한다. 어떤 시점에도 락은 최대 한 스레드만 보유할 수 있다.
   여기의 락은 "재귀적(recursive)"이 아니다. 즉, 현재 락을 보유한 스레드가
   다시 그 락을 획득하려 하면 오류가 된다.

   락은 초기값이 1인 세마포어의 특수한 형태다. 락과 세마포어의 차이는 두 가지다.
   첫째, 세마포어의 값은 1보다 클 수 있지만, 락은 한 번에 한 스레드만 소유할 수 있다.
   둘째, 세마포어에는 소유자 개념이 없어서 한 스레드가 "down"하고 다른 스레드가
   "up"할 수 있지만, 락은 같은 스레드가 획득(acquire)과 해제(release)를 모두 해야 한다.
   이러한 제약이 부담스럽다면 락 대신 세마포어를 사용하는 것이 적절한 신호다. */
void
lock_init (struct lock *lock) {
	ASSERT (lock != NULL);

	lock->holder = NULL;
	sema_init (&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */

/* LOCK을 획득한다. 필요하다면 사용할 수 있을 때까지 수면에 들어간다.
   현재 스레드는 이미 해당 락을 보유하고 있어서는 안 된다.

   이 함수는 수면할 수 있으므로 인터럽트 핸들러 내에서 호출하면 안 된다.
   인터럽트를 비활성화한 상태에서 호출할 수는 있지만, 수면이 필요하면
   인터럽트는 다시 켜지게 된다. */
void
lock_acquire (struct lock *lock) {
	ASSERT (lock != NULL);
	ASSERT (!intr_context ());
	ASSERT (!lock_held_by_current_thread (lock));

	struct thread * cur = thread_current();
	
	if (lock->holder != NULL) {
		enum intr_level old = intr_disable();
		cur->waiting_lock = lock;

		struct thread *hold = lock->holder;
		int depth = 0;

		while (hold && depth++ < 8) {
			if (cur->priority > hold->priority) {
				hold->priority = cur->priority;
            resort_ready_if_ready (hold);
			}
			if (hold->waiting_lock == NULL) break;
			hold = hold->waiting_lock->holder;
		}

		intr_set_level (old);
	}
	sema_down (&lock->semaphore);

	cur->waiting_lock = NULL;
	lock->holder = cur;
	list_push_back(&cur->locks, &lock->elem);
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */

/* LOCK을 획득 시도하고, 성공하면 true, 실패하면 false를 반환한다.
   현재 스레드는 이미 해당 락을 보유하고 있어서는 안 된다.

   이 함수는 수면하지 않으므로 인터럽트 핸들러 내에서 호출할 수 있다. */
bool
lock_try_acquire (struct lock *lock) {
	bool success;

	ASSERT (lock != NULL);
	ASSERT (!lock_held_by_current_thread (lock));

	success = sema_try_down (&lock->semaphore);
	if (success)
		lock->holder = thread_current ();
	return success;
}

/* Releases LOCK, which must be owned by the current thread.
   This is lock_release function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */

/* 현재 스레드가 보유 중인 LOCK을 해제한다.
   이 함수는 lock_release이다.

   인터럽트 핸들러는 락을 획득할 수 없으므로, 인터럽트 핸들러 내에서
   락을 해제하려 시도하는 것은 의미가 없다. */
void
lock_release (struct lock *lock) {
	ASSERT (lock != NULL);
	ASSERT (lock_held_by_current_thread (lock));
	enum intr_level old = intr_disable();

	struct thread * cur = thread_current();
	list_remove(&lock->elem);

	int base = cur->base_priority;
	struct list_elem *lock_ele;
	for(lock_ele = list_begin(&cur->locks);
		lock_ele != list_end(&cur->locks);
		lock_ele = list_next(lock_ele)) {
		struct lock *L = list_entry(lock_ele, struct lock, elem);
		if (!list_empty(&L->semaphore.waiters)) {
			struct thread *top = list_entry(list_max(&L->semaphore.waiters, prio_less, NULL),
                                      struct thread, elem);
			if (base < top->priority) base = top->priority;
		}
	}
	cur->priority = base;
   resort_ready_if_ready(cur);
	lock->holder = NULL;
	intr_set_level(old);
	sema_up (&lock->semaphore);
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */

/* 현재 스레드가 LOCK을 보유하고 있으면 true, 아니면 false를 반환한다.
   (다른 스레드가 락을 보유하는지 검사하는 것은 경쟁 상태를 만들 수 있으니 주의.) */
bool
lock_held_by_current_thread (const struct lock *lock) {
	ASSERT (lock != NULL);

	return lock->holder == thread_current ();
}

/* One semaphore in a list. */
/* 리스트 안의 하나의 세마포어 요소. */
struct semaphore_elem {
	struct list_elem elem;              /* List element. */
	/* 리스트 요소. */
	struct semaphore semaphore;         /* This semaphore. */
	/* 이 세마포어. */
};

static bool waiter_less (const struct list_elem *a,
                         const struct list_elem *b,
                         void *aux UNUSED) {
  const struct semaphore_elem *wa = list_entry (a, struct semaphore_elem, elem);
  const struct semaphore_elem *wb = list_entry (b, struct semaphore_elem, elem);

  int pa = list_empty(&wa->semaphore.waiters) ? PRI_MIN - 1
           : list_entry(list_front(&wa->semaphore.waiters), struct thread, elem)->priority;
  int pb = list_empty(&wb->semaphore.waiters) ? PRI_MIN - 1
           : list_entry(list_front(&wb->semaphore.waiters), struct thread, elem)->priority;
  return pa < pb;
}

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */

/* 조건 변수 COND를 초기화한다. 조건 변수는 어떤 코드가 조건을 신호로 알려주고,
   협력하는 다른 코드가 그 신호를 받아 동작할 수 있도록 한다. */
void
cond_init (struct condition *cond) {
	ASSERT (cond != NULL);

	list_init (&cond->waiters);
}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */

/* LOCK을 원자적으로 해제하고, 다른 코드가 COND에 신호를 보낼 때까지 기다린다.
   COND에 신호가 도착하면, 반환하기 전에 LOCK을 다시 획득한다.
   이 함수를 호출하기 전에 LOCK을 보유하고 있어야 한다.

   이 함수가 구현하는 모니터는 "Hoare" 스타일이 아니라 "Mesa" 스타일이다.
   즉, 신호를 보내는 것과 받는 것이 원자적 연산이 아니다.
   따라서 일반적으로 대기가 끝난 뒤 호출자는 조건을 다시 검사해야 하며,
   필요하다면 다시 기다려야 한다.

   하나의 조건 변수는 단 하나의 락과만 연관되지만,
   하나의 락은 여러 조건 변수와 연관될 수 있다.
   즉, 락에서 조건 변수로의 관계는 일대다 매핑이다.

   이 함수는 수면할 수 있으므로 인터럽트 핸들러 내에서 호출하면 안 된다.
   인터럽트를 비활성화한 상태에서 호출할 수는 있지만, 수면이 필요하면
   인터럽트는 다시 켜지게 된다. */
void
cond_wait (struct condition *cond, struct lock *lock) {
	struct semaphore_elem waiter;

	ASSERT (cond != NULL);
	ASSERT (lock != NULL);
	ASSERT (!intr_context ());
	ASSERT (lock_held_by_current_thread (lock));

	sema_init (&waiter.semaphore, 0);
	list_insert_ordered (&cond->waiters, &waiter.elem, greater_waiter, NULL);
	lock_release (lock);
	sema_down (&waiter.semaphore);
	lock_acquire (lock);
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */


static bool greater_waiter(const struct list_elem *a, const struct list_elem *b, void *aux UNUSED) {
    struct semaphore_elem *wa = list_entry(a, struct semaphore_elem, elem);
    struct semaphore_elem *wb = list_entry(b, struct semaphore_elem, elem);
	int pa = list_empty(&wa->semaphore.waiters) ? -1
									: list_entry(list_front(&wa->semaphore.waiters), struct thread, elem)->priority;
	int pb = list_empty(&wb->semaphore.waiters) ? -1
									: list_entry(list_front(&wb->semaphore.waiters), struct thread, elem)->priority;
    return pa > pb;
}

/* COND(LOCK으로 보호됨)에서 대기 중인 스레드가 있다면,
   그중 하나에 신호를 보내 대기에서 깨운다.
   이 함수를 호출하기 전에 LOCK을 보유하고 있어야 한다.

   인터럽트 핸들러는 락을 획득할 수 없으므로,
   인터럽트 핸들러 내에서 조건 변수에 신호를 보내려는 시도는 의미가 없다. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED) {
	ASSERT (cond != NULL);
	ASSERT (lock != NULL);
	ASSERT (!intr_context ());
	ASSERT (lock_held_by_current_thread (lock));

	if (!list_empty (&cond->waiters)){
		struct list_elem *best_elem = list_max(&cond->waiters, waiter_less, NULL);
		struct semaphore_elem *best = list_entry(best_elem, struct semaphore_elem, elem);
		list_remove(best_elem);
		sema_up (&best->semaphore);
	}
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */

/* COND(LOCK으로 보호됨)에서 대기 중인 모든 스레드를 깨운다(있다면).
   이 함수를 호출하기 전에 LOCK을 보유하고 있어야 한다.

   인터럽트 핸들러는 락을 획득할 수 없으므로,
   인터럽트 핸들러 내에서 조건 변수에 신호를 보내려는 시도는 의미가 없다. */
void
cond_broadcast (struct condition *cond, struct lock *lock) {
	ASSERT (cond != NULL);
	ASSERT (lock != NULL);

	while (!list_empty (&cond->waiters))
		cond_signal (cond, lock);
}
