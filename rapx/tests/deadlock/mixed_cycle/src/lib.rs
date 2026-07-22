#![no_std]
#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};

// ---- LockA ----

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

// ---- Interrupt API ----

#[rapx::IntrApi(Type = Disable, Nested = true)]
pub fn disable_irq() {}

#[rapx::IntrApi(Type = Enable, Nested = true)]
pub fn enable_irq() {}

// ---- Mixed-cycle deadlock scenario ----

static A: LockA<u32> = LockA::new(0);
static B: LockB<u32> = LockB::new(0);

/// ISR: acquires LockB in interrupt context.
/// This creates interrupt self-cycles on LockB (if also held in normal context).
#[rapx::IsrEntry]
fn isr_handler() {
    // ISR acquires LockB while possibly held by normal context
    let _b = B.lock();
}

/// Normal path: acquire A then B.
/// LockB has an interrupt self-cycle here (ISR also acquires LockB).
/// The normal edge A → B combined with the interrupt edge on B
/// forms a mixed 3-node cycle: A --normal--> B --interrupt--> B.
pub fn path_acquire_a_then_b() {
    let _a = A.lock();
    let _b = B.lock();
}

/// Normal path to trigger ABBA with path_acquire_a_then_b, plus ISR edges.
pub fn path_acquire_b_then_a() {
    let _b = B.lock();
    let _a = A.lock();
}
