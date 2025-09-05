#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "intrinsic.h"
#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
/* struct thread의 `magic` 필드에 넣는 난수값.
   스택 오버플로우를 감지하는 데 사용된다. 자세한 내용은 thread.h 상단의 큰 주석을 참고. */
#define THREAD_MAGIC 0xcd6abf4b

/* Random value for basic thread
   Do not modify this value. */
/* 기본 스레드를 나타내는 난수값.
   이 값은 수정하면 안 된다. */
#define THREAD_BASIC 0xd42df210

/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
/* THREAD_READY 상태(실행 준비는 되었지만 실제로 실행 중은 아님)에 있는 프로세스들의 리스트. */
static struct list ready_list;

/* Idle thread. */
/* 유휴(idle) 스레드. */
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
/* 초기 스레드, 즉 init.c의 main()을 실행 중인 스레드. */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
/* allocate_tid()에서 사용하는 락. */
static struct lock tid_lock;

/* Thread destruction requests */
/* 스레드 파괴 요청 큐(지연 해제용). */
static struct list destruction_req;

/* Statistics. */
/* 통계 정보. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
/* 유휴 상태로 보낸 타이머 틱 수. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
/* 커널 스레드에서 소비한 타이머 틱 수. */
static long long user_ticks;    /* # of timer ticks in user programs. */
/* 사용자 프로그램에서 소비한 타이머 틱 수. */

/* Scheduling. */
/* 스케줄링 관련. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
/* 각 스레드에 할당되는 타이머 틱 수(타임 슬라이스). */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */
/* 마지막 양보(yield) 이후 경과한 타이머 틱 수. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
/* false(기본값)이면 라운드 로빈 스케줄러를 사용.
   true이면 다단계 피드백 큐(MLFQS) 스케줄러를 사용.
   커널 커맨드라인 옵션 "-o mlfqs"로 제어된다. */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static void do_schedule(int status);
static void schedule (void);
static tid_t allocate_tid (void);

/* Returns true if T appears to point to a valid thread. */
/* T가 유효한 스레드를 가리키는 것으로 보이면 true를 반환. */
#define is_thread(t) ((t) != NULL && (t)->magic == THREAD_MAGIC)

/* Returns the running thread.
 * Read the CPU's stack pointer `rsp', and then round that
 * down to the start of a page.  Since `struct thread' is
 * always at the beginning of a page and the stack pointer is
 * somewhere in the middle, this locates the curent thread. */
/* 현재 실행 중인 스레드를 반환한다.
 * CPU의 스택 포인터 `rsp`를 읽고 페이지 시작 주소로 내림한다.
 * `struct thread`는 항상 페이지의 시작에 있고, 스택 포인터는 그 중간 어딘가를 가리키므로
 * 이를 통해 현재 스레드의 구조체를 찾을 수 있다. */
#define running_thread() ((struct thread *) (pg_round_down (rrsp ())))


// Global descriptor table for the thread_start.
// Because the gdt will be setup after the thread_init, we should
// setup temporal gdt first.
// thread_start를 위한 전역 기술자 테이블(GDT).
// gdt는 thread_init 이후에 설정되므로, 우선 임시 gdt를 먼저 설정해야 한다.
static uint64_t gdt[3] = { 0, 0x00af9a000000ffff, 0x00cf92000000ffff };

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
/* 현재 실행 중인 코드를 스레드로 변환하여 스레딩 시스템을 초기화한다.
   일반적으로 가능한 방식은 아니지만, loader.S가 스택의 바닥을 페이지 경계에 맞추었기 때문에
   여기서는 가능하다.

   또한 런 큐와 tid 락을 초기화한다.

   이 함수를 호출한 뒤에는 thread_create()로 스레드를 만들기 전에
   반드시 페이지 할당자(page allocator)를 초기화해야 한다.

   이 함수가 끝나기 전까지 thread_current()를 호출하는 것은 안전하지 않다. */
void
thread_init (void) {
	ASSERT (intr_get_level () == INTR_OFF);

	/* Reload the temporal gdt for the kernel
	 * This gdt does not include the user context.
	 * The kernel will rebuild the gdt with user context, in gdt_init (). */
	/* 커널을 위한 임시 gdt를 다시 로드한다.
	 * 이 gdt에는 사용자 컨텍스트가 포함되어 있지 않다.
	 * 커널은 gdt_init()에서 사용자 컨텍스트를 포함한 gdt를 다시 구성한다. */
	struct desc_ptr gdt_ds = {
		.size = sizeof (gdt) - 1,
		.address = (uint64_t) gdt
	};
	lgdt (&gdt_ds);

	/* Init the globla thread context */
	/* 전역 스레드 컨텍스트 초기화 */
	lock_init (&tid_lock);
	list_init (&ready_list);
	list_init (&destruction_req);

	/* Set up a thread structure for the running thread. */
	/* 현재 실행 중인 스레드를 위한 thread 구조체를 설정. */
	initial_thread = running_thread ();
	init_thread (initial_thread, "main", PRI_DEFAULT);
	initial_thread->status = THREAD_RUNNING;
	initial_thread->tid = allocate_tid ();
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
/* 인터럽트를 활성화하여 선점형 스레드 스케줄링을 시작한다.
   또한 idle 스레드를 생성한다. */
void
thread_start (void) {
	/* Create the idle thread. */
	/* idle 스레드 생성 */
	struct semaphore idle_started;
	sema_init (&idle_started, 0);
	thread_create ("idle", PRI_MIN, idle, &idle_started);

	/* Start preemptive thread scheduling. */
	/* 선점형 스케줄링 시작 */
	intr_enable ();

	/* Wait for the idle thread to initialize idle_thread. */
	/* idle 스레드가 idle_thread 포인터를 초기화할 때까지 대기 */
	sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
/* 매 타이머 틱마다 타이머 인터럽트 핸들러가 호출한다.
   따라서 이 함수는 외부 인터럽트 컨텍스트에서 실행된다. */
void
thread_tick (void) {
	struct thread *t = thread_current ();

	/* Update statistics. */
	/* 통계 정보 갱신 */
	if (t == idle_thread)
		idle_ticks++;
#ifdef USERPROG
	else if (t->pml4 != NULL)
		user_ticks++;
#endif
	else
		kernel_ticks++;

	/* Enforce preemption. */
	/* 선점을 강제(타임 슬라이스 소진 시 양보) */
	if (++thread_ticks >= TIME_SLICE)
		intr_yield_on_return ();
}

/* Prints thread statistics. */
/* 스레드 관련 통계를 출력한다. */
void
thread_print_stats (void) {
	printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
			idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
/* NAME이라는 이름과 초기 PRIORITY를 가진 새로운 커널 스레드를 생성한다.
   이 스레드는 FUNCTION(AUX)를 실행하며, 생성 후 ready 큐에 추가된다.
   성공 시 새 스레드의 tid를 반환하고, 실패 시 TID_ERROR를 반환한다.

   thread_start()가 이미 호출된 상태라면, thread_create()가 리턴하기 전에
   새 스레드가 스케줄될 수도 있고, 심지어 리턴 전에 종료될 수도 있다.
   반대로, 새 스레드가 스케줄되기 전에 현재 스레드가 오랫동안 계속 실행될 수도 있다.
   순서를 보장해야 한다면 세마포어나 다른 동기화 수단을 이용하라.

   제공된 코드는 새 스레드의 `priority` 필드를 PRIORITY로 설정만 할 뿐,
   실제 우선순위 스케줄링은 구현되어 있지 않다.
   우선순위 스케줄링은 과제 1-3의 목표다. */
tid_t
thread_create (const char *name, int priority,
		thread_func *function, void *aux) {
	struct thread *t;
	tid_t tid;

	ASSERT (function != NULL);

	/* Allocate thread. */
	/* 스레드 구조체 페이지 할당 */
	t = palloc_get_page (PAL_ZERO);
	if (t == NULL)
		return TID_ERROR;

	/* Initialize thread. */
	/* 스레드 초기화 */
	init_thread (t, name, priority);
	tid = t->tid = allocate_tid ();

	/* Call the kernel_thread if it scheduled.
	 * Note) rdi is 1st argument, and rsi is 2nd argument. */
	/* 스케줄되면 kernel_thread가 호출되도록 초기 컨텍스트 설정.
	 * 참고) rdi가 첫 번째 인자, rsi가 두 번째 인자 레지스터이다. */
	t->tf.rip = (uintptr_t) kernel_thread;
	t->tf.R.rdi = (uint64_t) function;
	t->tf.R.rsi = (uint64_t) aux;
	t->tf.ds = SEL_KDSEG;
	t->tf.es = SEL_KDSEG;
	t->tf.ss = SEL_KDSEG;
	t->tf.cs = SEL_KCSEG;
	t->tf.eflags = FLAG_IF;

	/* Add to run queue. */
	/* 실행 준비 큐(ready queue)에 추가 */
	thread_unblock (t);

	return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
/* 현재 스레드를 수면(sleep) 상태로 전환한다.
   thread_unblock()으로 깨울 때까지 스케줄되지 않는다.

   이 함수는 반드시 인터럽트가 비활성화된 상태에서 호출해야 한다.
   일반적으로는 synch.h의 동기화 원시들을 사용하는 편이 더 좋다. */
void
thread_block (void) {
	ASSERT (!intr_context ());
	ASSERT (intr_get_level () == INTR_OFF);
	thread_current ()->status = THREAD_BLOCKED;
	schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
/* 차단(blocked)된 스레드 T를 실행 준비(ready) 상태로 전환한다.
   T가 blocked 상태가 아니라면 오류이다. (실행 중인 스레드를 ready로 만들고 싶다면
   thread_yield()를 사용하라.)

   이 함수는 현재 실행 중인 스레드를 선점하지 않는다.
   이는 중요할 수 있는데, 호출자가 직접 인터럽트를 비활성화한 상태라면
   스레드를 원자적으로 unblock하고 다른 데이터도 갱신하길 기대할 수 있기 때문이다. */
void
thread_unblock (struct thread *t) {
	enum intr_level old_level;

	ASSERT (is_thread (t));

	old_level = intr_disable ();
	ASSERT (t->status == THREAD_BLOCKED);
	list_push_back (&ready_list, &t->elem);
	t->status = THREAD_READY;
	intr_set_level (old_level);
}

/* Returns the name of the running thread. */
/* 현재 실행 중인 스레드의 이름을 반환. */
const char *
thread_name (void) {
	return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
/* 현재 실행 중인 스레드를 반환.
   running_thread()에 몇 가지 안전성 검사를 추가한 버전.
   자세한 내용은 thread.h 상단의 큰 주석을 참고. */
struct thread *
thread_current (void) {
	struct thread *t = running_thread ();

	/* Make sure T is really a thread.
	   If either of these assertions fire, then your thread may
	   have overflowed its stack.  Each thread has less than 4 kB
	   of stack, so a few big automatic arrays or moderate
	   recursion can cause stack overflow. */
	/* T가 실제 스레드인지 확인한다.
	   아래 단언문 중 하나가 실패하면, 스레드의 스택이 오버플로우 되었을 가능성이 있다.
	   각 스레드의 스택은 4 kB보다 작으므로, 큰 자동 배열 몇 개나
	   적당한 수준의 재귀만으로도 스택 오버플로우가 발생할 수 있다. */
	ASSERT (is_thread (t));
	ASSERT (t->status == THREAD_RUNNING);

	return t;
}

/* Returns the running thread's tid. */
/* 현재 실행 중인 스레드의 tid를 반환. */
tid_t
thread_tid (void) {
	return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
/* 현재 스레드를 스케줄에서 제거하고 파괴한다.
   이 함수는 호출자에게 절대 돌아오지 않는다. */
void
thread_exit (void) {
	ASSERT (!intr_context ());

#ifdef USERPROG
	process_exit ();
#endif

	/* Just set our status to dying and schedule another process.
	   We will be destroyed during the call to schedule_tail(). */
	/* 상태를 DYING으로 설정하고 다른 프로세스를 스케줄한다.
	   실제 파괴는 schedule_tail() 호출 중에 수행된다. */
	intr_disable ();
	do_schedule (THREAD_DYING);
	NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
/* CPU를 양보한다. 현재 스레드는 수면 상태로 가지 않으며,
   스케줄러의 판단에 따라 즉시 다시 스케줄될 수도 있다. */
void
thread_yield (void) {
	struct thread *curr = thread_current ();
	enum intr_level old_level;

	ASSERT (!intr_context ());

	old_level = intr_disable ();
	if (curr != idle_thread)
		list_push_back (&ready_list, &curr->elem);
	do_schedule (THREAD_READY);
	intr_set_level (old_level);
}

/* Sets the current thread's priority to NEW_PRIORITY. */
/* 현재 스레드의 우선순위를 NEW_PRIORITY로 설정. */
void
thread_set_priority (int new_priority) {
	thread_current ()->priority = new_priority;
}

/* Returns the current thread's priority. */
/* 현재 스레드의 우선순위를 반환. */
int
thread_get_priority (void) {
	return thread_current ()->priority;
}

/* Sets the current thread's nice value to NICE. */
/* 현재 스레드의 nice 값을 NICE로 설정. */
void
thread_set_nice (int nice UNUSED) {
	/* TODO: Your implementation goes here */
	/* TODO: 여기에 구현 */
}

/* Returns the current thread's nice value. */
/* 현재 스레드의 nice 값을 반환. */
int
thread_get_nice (void) {
	/* TODO: Your implementation goes here */
	/* TODO: 여기에 구현 */
	return 0;
}

/* Returns 100 times the system load average. */
/* 시스템 load average * 100 값을 반환. */
int
thread_get_load_avg (void) {
	/* TODO: Your implementation goes here */
	/* TODO: 여기에 구현 */
	return 0;
}

/* Returns 100 times the current thread's recent_cpu value. */
/* 현재 스레드의 recent_cpu * 100 값을 반환. */
int
thread_get_recent_cpu (void) {
	/* TODO: Your implementation goes here */
	/* TODO: 여기에 구현 */
	return 0;
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
/* 유휴 스레드. 실행 가능한 다른 스레드가 없을 때 동작한다.

   idle 스레드는 처음에 thread_start()에 의해 ready 리스트에 들어간다.
   처음 한 번 스케줄된 후 idle_thread 포인터를 초기화하고,
   thread_start()가 진행될 수 있도록 건네받은 세마포어를 "up" 한 뒤
   즉시 블록된다. 그 이후로 idle 스레드는 ready 리스트에 나타나지 않는다.
   ready 리스트가 비어 있을 때만 next_thread_to_run()이 특별히 이 스레드를 반환한다. */
static void
idle (void *idle_started_ UNUSED) {
	struct semaphore *idle_started = idle_started_;

	idle_thread = thread_current ();
	sema_up (idle_started);

	for (;;) {
		/* Let someone else run. */
		/* 다른 스레드가 실행되도록 양보 */
		intr_disable ();
		thread_block ();

		/* Re-enable interrupts and wait for the next one.

		   The `sti' instruction disables interrupts until the
		   completion of the next instruction, so these two
		   instructions are executed atomically.  This atomicity is
		   important; otherwise, an interrupt could be handled
		   between re-enabling interrupts and waiting for the next
		   one to occur, wasting as much as one clock tick worth of
		   time.

		   See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
		   7.11.1 "HLT Instruction". */
		/* 인터럽트를 다시 활성화하고, 다음 인터럽트를 기다린다.

		   `sti` 명령은 다음 명령이 완료될 때까지 인터럽트를 비활성화하므로
		   아래 두 명령은 원자적으로 실행된다. 이 원자성은 중요하다.
		   그렇지 않으면 인터럽트를 다시 활성화한 직후와 다음 인터럽트를
		   기다리는 사이에 인터럽트가 처리되어, 최대 한 틱만큼 시간을 낭비할 수 있다.

		   참고: [IA32-v2a] "HLT", [IA32-v2b] "STI", [IA32-v3a] 7.11.1 "HLT Instruction". */
		asm volatile ("sti; hlt" : : : "memory");
	}
}

/* Function used as the basis for a kernel thread. */
/* 커널 스레드의 기본 엔트리 함수로 사용되는 래퍼. */
static void
kernel_thread (thread_func *function, void *aux) {
	ASSERT (function != NULL);

	intr_enable ();       /* The scheduler runs with interrupts off. */
	/* 스케줄러는 인터럽트 비활성 상태에서 동작하므로, 여기서 인터럽트를 활성화. */
	function (aux);       /* Execute the thread function. */
	/* 스레드 함수 실행. */
	thread_exit ();       /* If function() returns, kill the thread. */
	/* function()이 리턴하면 스레드를 종료. */
}


/* Does basic initialization of T as a blocked thread named
   NAME. */
/* T를 NAME이라는 이름의 BLOCKED 상태 스레드로 기본 초기화. */
static void
init_thread (struct thread *t, const char *name, int priority) {
	ASSERT (t != NULL);
	ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
	ASSERT (name != NULL);

	memset (t, 0, sizeof *t);
	t->status = THREAD_BLOCKED;
	strlcpy (t->name, name, sizeof t->name);
	t->tf.rsp = (uint64_t) t + PGSIZE - sizeof (void *);
	t->priority = priority;
	t->magic = THREAD_MAGIC;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
/* 다음에 스케줄할 스레드를 선택하여 반환한다.
   런 큐가 비어 있지 않다면 런 큐에서 하나를 반환해야 한다.
   (현재 실행 중인 스레드가 계속 실행 가능하다면 런 큐에 들어있다.)
   런 큐가 비어 있다면 idle_thread를 반환한다. */
static struct thread *
next_thread_to_run (void) {
	if (list_empty (&ready_list))
		return idle_thread;
	else
		return list_entry (list_pop_front (&ready_list), struct thread, elem);
}

/* Use iretq to launch the thread */
/* iretq 명령을 사용해 스레드를 런치(문맥 복원 후 전환)한다. */
void
do_iret (struct intr_frame *tf) {
	__asm __volatile(
			"movq %0, %%rsp\n"
			"movq 0(%%rsp),%%r15\n"
			"movq 8(%%rsp),%%r14\n"
			"movq 16(%%rsp),%%r13\n"
			"movq 24(%%rsp),%%r12\n"
			"movq 32(%%rsp),%%r11\n"
			"movq 40(%%rsp),%%r10\n"
			"movq 48(%%rsp),%%r9\n"
			"movq 56(%%rsp),%%r8\n"
			"movq 64(%%rsp),%%rsi\n"
			"movq 72(%%rsp),%%rdi\n"
			"movq 80(%%rsp),%%rbp\n"
			"movq 88(%%rsp),%%rdx\n"
			"movq 96(%%rsp),%%rcx\n"
			"movq 104(%%rsp),%%rbx\n"
			"movq 112(%%rsp),%%rax\n"
			"addq $120,%%rsp\n"
			"movw 8(%%rsp),%%ds\n"
			"movw (%%rsp),%%es\n"
			"addq $32, %%rsp\n"
			"iretq"
			: : "g" ((uint64_t) tf) : "memory");
}

/* Switching the thread by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function. */
/* 새 스레드의 페이지 테이블을 활성화함으로써 스레드를 전환하고,
   이전 스레드가 DYING 상태라면 파괴한다.

   이 함수가 호출될 때는 방금 이전 스레드(PREV)에서 전환되어
   새 스레드가 이미 실행 중이며, 인터럽트는 여전히 비활성화되어 있다.

   스레드 전환이 끝나기 전에는 printf()를 호출하는 것이 안전하지 않다.
   실제로는 이 함수의 끝부분에서만 printf()를 호출해야 한다는 의미다. */
static void
thread_launch (struct thread *th) {
	uint64_t tf_cur = (uint64_t) &running_thread ()->tf;
	uint64_t tf = (uint64_t) &th->tf;
	ASSERT (intr_get_level () == INTR_OFF);

	/* The main switching logic.
	 * We first restore the whole execution context into the intr_frame
	 * and then switching to the next thread by calling do_iret.
	 * Note that, we SHOULD NOT use any stack from here
	 * until switching is done. */
	/* 전환의 핵심 로직.
	 * 먼저 현재 실행 컨텍스트를 intr_frame에 저장(복구용)하고,
	 * do_iret를 호출하여 다음 스레드로 전환한다.
	 * 주의: 전환이 완료될 때까지는 이 지점 이후의 스택을 사용해서는 안 된다. */
	__asm __volatile (
			/* Store registers that will be used. */
			/* 사용할 레지스터들을 저장한다. */
			"push %%rax\n"
			"push %%rbx\n"
			"push %%rcx\n"
			/* Fetch input once */
			/* 입력 인자를 한 번만 로드한다. */
			"movq %0, %%rax\n"
			"movq %1, %%rcx\n"
			"movq %%r15, 0(%%rax)\n"
			"movq %%r14, 8(%%rax)\n"
			"movq %%r13, 16(%%rax)\n"
			"movq %%r12, 24(%%rax)\n"
			"movq %%r11, 32(%%rax)\n"
			"movq %%r10, 40(%%rax)\n"
			"movq %%r9, 48(%%rax)\n"
			"movq %%r8, 56(%%rax)\n"
			"movq %%rsi, 64(%%rax)\n"
			"movq %%rdi, 72(%%rax)\n"
			"movq %%rbp, 80(%%rax)\n"
			"movq %%rdx, 88(%%rax)\n"
			"pop %%rbx\n"              // Saved rcx
			// rcx를 pop하여 복원(저장)한 값.
			"movq %%rbx, 96(%%rax)\n"
			"pop %%rbx\n"              // Saved rbx
			// rbx를 pop하여 복원(저장)한 값.
			"movq %%rbx, 104(%%rax)\n"
			"pop %%rbx\n"              // Saved rax
			// rax를 pop하여 복원(저장)한 값.
			"movq %%rbx, 112(%%rax)\n"
			"addq $120, %%rax\n"
			"movw %%es, (%%rax)\n"
			"movw %%ds, 8(%%rax)\n"
			"addq $32, %%rax\n"
			"call __next\n"         // read the current rip.
			// 현재 rip를 읽어오기 위한 콜.
			"__next:\n"
			"pop %%rbx\n"
			"addq $(out_iret -  __next), %%rbx\n"
			"movq %%rbx, 0(%%rax)\n" // rip
			// rip 저장.
			"movw %%cs, 8(%%rax)\n"  // cs
			// cs 저장.
			"pushfq\n"
			"popq %%rbx\n"
			"mov %%rbx, 16(%%rax)\n" // eflags
			// eflags 저장.
			"mov %%rsp, 24(%%rax)\n" // rsp
			// rsp 저장.
			"movw %%ss, 32(%%rax)\n"
			// ss 저장.
			"mov %%rcx, %%rdi\n"
			"call do_iret\n"
			"out_iret:\n"
			: : "g"(tf_cur), "g" (tf) : "memory"
			);
}

/* Schedules a new process. At entry, interrupts must be off.
 * This function modify current thread's status to status and then
 * finds another thread to run and switches to it.
 * It's not safe to call printf() in the schedule(). */
/* 새 프로세스를 스케줄한다. 진입 시 인터럽트는 꺼져 있어야 한다.
 * 이 함수는 현재 스레드의 상태를 인자로 받은 status로 바꾸고,
 * 실행할 다른 스레드를 찾아 전환한다.
 * schedule() 안에서 printf()를 호출하는 것은 안전하지 않다. */
static void
do_schedule(int status) {
	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (thread_current()->status == THREAD_RUNNING);
	while (!list_empty (&destruction_req)) {
		struct thread *victim =
			list_entry (list_pop_front (&destruction_req), struct thread, elem);
		palloc_free_page(victim);
	}
	thread_current ()->status = status;
	schedule ();
}

static void
schedule (void) {
	struct thread *curr = running_thread ();
	struct thread *next = next_thread_to_run ();

	ASSERT (intr_get_level () == INTR_OFF);
	ASSERT (curr->status != THREAD_RUNNING);
	ASSERT (is_thread (next));
	/* Mark us as running. */
	/* next를 RUNNING 상태로 표시 */
	next->status = THREAD_RUNNING;

	/* Start new time slice. */
	/* 새 타임 슬라이스 시작 */
	thread_ticks = 0;

#ifdef USERPROG
	/* Activate the new address space. */
	/* 새로운 주소 공간 활성화 */
	process_activate (next);
#endif

	if (curr != next) {
		/* If the thread we switched from is dying, destroy its struct
		   thread. This must happen late so that thread_exit() doesn't
		   pull out the rug under itself.
		   We just queuing the page free reqeust here because the page is
		   currently used by the stack.
		   The real destruction logic will be called at the beginning of the
		   schedule(). */
		/* 전환 대상이 된 이전 스레드가 DYING이라면, 그 thread 구조체를 파괴한다.
		   thread_exit()가 실행 중인 자신의 기반을 무너뜨리지 않도록 늦게 처리해야 한다.
		   현재 페이지는 스택에서 사용 중이므로 여기서는 페이지 해제를 큐에 넣기만 한다.
		   실제 파괴 로직은 다음 schedule() 시작 시점에 수행된다. */
		if (curr && curr->status == THREAD_DYING && curr != initial_thread) {
			ASSERT (curr != next);
			list_push_back (&destruction_req, &curr->elem);
		}

		/* Before switching the thread, we first save the information
		 * of current running. */
		/* 스레드를 전환하기 전에, 현재 실행 중인 상태 정보를 먼저 저장한다. */
		thread_launch (next);
	}
}

/* Returns a tid to use for a new thread. */
/* 새 스레드에 사용할 tid를 반환. */
static tid_t
allocate_tid (void) {
	static tid_t next_tid = 1;
	tid_t tid;

	lock_acquire (&tid_lock);
	tid = next_tid++;
	lock_release (&tid_lock);

	return tid;
}
