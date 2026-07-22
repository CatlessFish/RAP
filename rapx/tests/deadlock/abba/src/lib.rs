#![no_std]
#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};

#[rapx::LockType(Name = "LockA")]
pub struct LockA<T> {
    val: UnsafeCell<T>,
}

impl<T> LockA<T> {
    pub const fn new(val: T) -> Self {
        Self {
            val: UnsafeCell::new(val),
        }
    }

    #[rapx::LockOp(LockArg = 0, GuardIrqDisabled = false)]
    pub fn lock(&self) -> LockAGuard<'_, T> {
        LockAGuard { lock: self }
    }
}

unsafe impl<T: Send> Sync for LockA<T> {}

#[rapx::LockGuardType(Name = "LockAGuard")]
pub struct LockAGuard<'a, T> {
    lock: &'a LockA<T>,
}

impl<T> Deref for LockAGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.val.get() }
    }
}

impl<T> DerefMut for LockAGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.val.get() }
    }
}

// ---- LockB ----

#[rapx::LockType(Name = "LockB")]
pub struct LockB<T> {
    val: UnsafeCell<T>,
}

impl<T> LockB<T> {
    pub const fn new(val: T) -> Self {
        Self {
            val: UnsafeCell::new(val),
        }
    }

    #[rapx::LockOp(LockArg = 0, GuardIrqDisabled = false)]
    pub fn lock(&self) -> LockBGuard<'_, T> {
        LockBGuard { lock: self }
    }
}

unsafe impl<T: Send> Sync for LockB<T> {}

#[rapx::LockGuardType(Name = "LockBGuard")]
pub struct LockBGuard<'a, T> {
    lock: &'a LockB<T>,
}

impl<T> Deref for LockBGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.val.get() }
    }
}

impl<T> DerefMut for LockBGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.val.get() }
    }
}

// ---- ABBA deadlock scenario (pure normal-edge cycle) ----

static A: LockA<u32> = LockA::new(0);
static B: LockB<u32> = LockB::new(0);

/// Thread 1: acquires A then B.
pub fn thread1() {
    let _a = A.lock();
    let _b = B.lock();
}

/// Thread 2: acquires B then A — ABBA deadlock with thread1.
pub fn thread2() {
    let _b = B.lock();
    let _a = A.lock();
}
