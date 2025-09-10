#ifndef THREADS_FIXED_POINT_H
#define THREADS_FIXED_POINT_H

#include <stdint.h>

/* 소수부 비트 수(q)와 배수 f=2^q. 여기서는 14비트 사용(17.14). */
#define Q 14
#define F (1 << Q)

/* 형식 별칭: 읽기 편하게 int32_t 사용 */
typedef int32_t fp_t;


/* ---------- 변환 계열 ---------- */

/* 정수 n -> 고정소수점 */
#define INT_TO_FP(n) ((fp_t)((n) * F))

/* 고정소수점 x -> 정수 (0쪽 절삭; truncate) */
#define FP_TO_INT_ZERO(x) ((int)((x) / F))

/* 고정소수점 x -> 정수 (반올림; round to nearest) */
#define FP_TO_INT_NEAR(x) ((int)(( (x) >= 0 ? (x) + F/2 : (x) - F/2 ) / F))


/* ---------- 기본 연산 ---------- */

/* 고정 + 고정 */
#define FP_ADD(x, y) ((fp_t)((x) + (y)))

/* 고정 - 고정 */
#define FP_SUB(x, y) ((fp_t)((x) - (y)))

/* 고정 + 정수 */
#define FP_ADD_INT(x, n) ((fp_t)((x) + (n) * F))

/* 고정 - 정수 */
#define FP_SUB_INT(x, n) ((fp_t)((x) - (n) * F))

/* 고정 × 정수 */
#define FP_MUL_INT(x, n) ((fp_t)((x) * (n)))

/* 고정 ÷ 정수 */
#define FP_DIV_INT(x, n) ((fp_t)((x) / (n)))


/* ---------- 고정 × 고정 / 고정 ÷ 고정 (중간 64비트 필수) ---------- */

/* 고정 × 고정:
 * - (x * y)는 스케일이 f^2가 되므로 /f로 되돌림
 * - 오버플로 방지를 위해 중간 계산은 64비트로
 */
#define FP_MUL(x, y) ((fp_t)(( (int64_t)(x) * (y) ) / F))

/* 고정 ÷ 고정:
 * - (x / y)는 스케일이 1/f가 되므로, 먼저 x*f를 해서 스케일 맞춘 뒤 /y
 * - 역시 64비트 중간형을 사용
 */
#define FP_DIV(x, y) ((fp_t)(( (int64_t)(x) * F ) / (y)))


#define FP_59_60 ((int32_t)(( (int64_t)59 * F ) / 60))                        /* 59/60 */
#define FP_1_60  ((int32_t)(( (int64_t) 1 * F ) / 60))                        /*  1/60 */

#endif