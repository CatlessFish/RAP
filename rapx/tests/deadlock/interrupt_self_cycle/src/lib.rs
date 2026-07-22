#![no_std]
#![feature(register_tool)]
#![register_tool(rapx)]
#![allow(dead_code)]

use core::cell::UnsafeCell;
use core::ops::{Deref, DerefMut};

#[rapx::LockType(Name = "SpinLock")]
pub struct SpinLock<T> {
    val: UnsafeCell<T>,
}

impl<T> SpinLock<T> {
    pub const fn new(val: T) -> Self {
        Self {
            val: UnsafeCell::new(val),
        }
    }

    #[rapx::LockOp(LockArg = 0, GuardIrqDisabled = false)]
    pub fn lock(&self) -> SpinLockGuard<'_, T> {
        SpinLockGuard { lock: self }
    }
}

unsafe impl<T: Send> Sync for SpinLock<T> {}

#[rapx::LockGuardType(Name = "SpinLockGuard")]
pub struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<T> Deref for SpinLockGuard<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.val.get() }
    }
}

impl<T> DerefMut for SpinLockGuard<'_, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.val.get() }
    }
}

// ---- Interrupt control API ----

#[rapx::IntrApi(Type = Disable, Nested = true)]
pub fn disable_irq() {
    // Real implementation would disable local interrupts on the CPU.
}

/// Re-enables local interrupts (called implicitly when the IRQ guard drops).
#[rapx::IntrApi(Type = Enable, Nested = true)]
pub fn enable_irq() {
    // Real implementation would re-enable local interrupts.
}

// ---- The deadlock scenario ----

/// A shared lock that can be accessed from both normal and ISR context.
static SERIAL_PORT: SpinLock<u32> = SpinLock::new(0);

/// ISR entry point: acquires SERIAL_PORT in interrupt context.
/// If an interrupt fires while normal_print() holds SERIAL_PORT,
/// this ISR will spin-wait forever — deadlock.
#[rapx::IsrEntry]
fn serial_isr() {
    let _guard = SERIAL_PORT.lock();
    // ... access serial port registers ...
}

/// Normal context: holds SERIAL_PORT.
/// The lock is acquired without disabling interrupts, so an ISR can fire
/// at any point within this critical section and attempt to re-acquire
/// the same lock.
pub fn normal_print() {
    let _guard = SERIAL_PORT.lock();
    // If serial_isr fires here, deadlock.
}
