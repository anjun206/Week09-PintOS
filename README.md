# Week09 - Team2 🖥️  
**PintOS Project - Main Branch**

---

## 📌 Project Overview
본 프로젝트는 **PintOS 운영체제**의 스레드(Thread) 부분을 구현하고 테스트한 결과를 정리한 것입니다.  
구현한 기능은 다음과 같습니다:

- **Threads**
  - Alarm Clock
  - Priority Scheduling
  - Advanced Scheduler

---

## ✅ Test Results

### 🔔 Alarm Clock
| Test | Result |
|------|--------|
| alarm-single       | ✅ PASS |
| alarm-multiple     | ✅ PASS |
| alarm-simultaneous | ✅ PASS |
| alarm-priority     | ✅ PASS |
| alarm-zero         | ✅ PASS |
| alarm-negative     | ✅ PASS |

### ⚡ Priority Scheduling
| Test | Result |
|------|--------|
| priority-change          | ✅ PASS |
| priority-donate-one      | ✅ PASS |
| priority-donate-multiple | ✅ PASS |
| priority-donate-multiple2| ✅ PASS |
| priority-donate-nest     | ✅ PASS |
| priority-donate-sema     | ✅ PASS |
| priority-donate-lower    | ✅ PASS |
| priority-fifo            | ✅ PASS |
| priority-preempt         | ✅ PASS |
| priority-sema            | ✅ PASS |
| priority-condvar         | ✅ PASS |
| priority-donate-chain    | ✅ PASS |

### 📊 Advanced Scheduler (MLFQS)
| Test | Result |
|------|--------|
| mlfqs-load-1   | ✅ PASS |
| mlfqs-load-60  | ✅ PASS |
| mlfqs-load-avg | ✅ PASS |
| mlfqs-recent-1 | ✅ PASS |
| mlfqs-fair-2   | ✅ PASS |
| mlfqs-fair-20  | ✅ PASS |
| mlfqs-nice-2   | ✅ PASS |
| mlfqs-nice-10  | ✅ PASS |

---

## 📂 Summary
- **Alarm Clock**: 모든 테스트 **성공** 🎉  
- **Priority Scheduling**: 모든 테스트 **성공** 🎉 
- **Advanced Scheduler**: 모든 테스트 **성공** 🎉 
---


## 👨‍💻 Team Info
- **Team Name**: Team2  
- **Project Week**: Week09  
- **Branch**: `main`

---

## 📝 Notes
- 클리어
