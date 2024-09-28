#![no_main]

use std::{alloc, ptr, fmt};

/// A stack data structure that holds elements of type `T`.
///
/// Implements all standard stack APIs.
struct Stack<T> {
    len: usize,
    cap: usize,
    buf: *mut T,
    layout: alloc::Layout,
}

impl<T> Stack<T> {
    const INITIAL_CAP: usize = 2;

    #[inline]
    pub fn new() -> Self {
        let cap = Self::INITIAL_CAP;
        let layout = Self::get_layout(cap);
        let buf = Self::alloc_new_buf(layout);
        Self { len: 0, cap: 2, buf, layout }
    }

    /// Creates a new stack with the specified capacity.
    ///
    /// # Panics
    ///
    /// Make sure that cap > 0
    #[inline]
    pub fn with_capacity(cap: usize) -> Self {
        // Used for safety.
        assert_ne!(cap, 0, "The capacity must not be 0");

        let layout = Self::get_layout(cap);
        let buf = Self::alloc_new_buf(layout);
        Self { len: 0, cap, buf, layout }
    }

    /// Pushes an element onto the stack.
    ///
    /// If the stack is at capacity, it grows the underlying buffer.
    #[inline]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap {
            self.grow();
        }

        // Safety: self.buf is guaranteed to be valid and have space for self.len elements
        unsafe { ptr::write(self.buf.add(self.len), elem); };

        self.len += 1;
    }

    #[inline]
    fn grow(&mut self) {
        let old_layout = self.layout;
        let old_buf = self.buf;

        self.cap *= 2;
        self.layout = Self::get_layout(self.cap);
        self.buf = Self::alloc_new_buf(self.layout);

        // Safety: old_buf and old_layout are guaranteed to be
        // valid and have space for self.len elements
        unsafe { ptr::copy(old_buf, self.buf, self.len); };

        Self::dealloc_old_buf(old_buf, old_layout);
    }

    #[inline]
    fn get_layout(cap: usize) -> alloc::Layout {
        // Safety: This will only error if `(sizeof(T) * cap) > isize::MAX` which will never happen
        unsafe { alloc::Layout::array::<T>(cap).unwrap_unchecked() }
    }

    #[inline]
    fn alloc_new_buf(layout: alloc::Layout) -> *mut T {
        // Safety: layout is guaranteed to be valid
        let ptr = unsafe { alloc::alloc(layout) };
        ptr as *mut T
    }

    #[inline]
    fn dealloc_old_buf(ptr: *mut T, layout: alloc::Layout) {
        // Safety: ptr and layout are guaranteed to be valid
        unsafe { alloc::dealloc(ptr as *mut u8, layout) }
    }

    /// Gets a reference to the element at the given index, if it exists.
    ///
    /// Safe version of [`Stack::get_unchecked`]
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len {
            return None;
        }

        Some(unsafe { self.get_unchecked(index) })
    }

    /// # Safety
    ///
    /// Make sure the index is in bounds
    #[inline]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*(self.buf.add(index))
    }

    /// Safe version of [`Stack::drop_unchecked`]
    ///
    /// Removes the last element from the stack without returning it like [`Stack::pop`].
    ///
    /// # Panics
    ///
    /// Make sure that length is non-zero
    #[inline]
    pub fn drop(&mut self) {
        assert!(!self.is_empty(), "Cannot drop non-empty stack");

        unsafe { self.drop_unchecked() }
    }

    /// Removes the last element from the stack without returning it like [`Stack::pop_unchecked`].
    ///
    /// # Safety
    ///
    /// Make sure that length is non-zero
    #[inline]
    pub unsafe fn drop_unchecked(&mut self) -> () {
        self.len -= 1;
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn cap(&self) -> usize {
        self.cap
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Clears the stack, removing all elements.
    #[inline]
    pub fn clear(&mut self) {
        self.len = 0;
    }

    /// Gets a reference to the last element of the stack, if it exists.
    ///
    /// Safe version of [`Stack::peek_unchecked`]
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }

        Some(unsafe { self.get_unchecked(self.len - 1) })
    }

    /// # Safety
    ///
    /// Make sure that length is non-zero
    #[inline]
    pub fn peek_unchecked(&self) -> &T {
        unsafe { self.get_unchecked(self.len - 1) }
    }

    /// Pops an element from the stack, returning it if it exists.
    ///
    /// Safe version of [`Stack::pop_unchecked`]
    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        Some(unsafe { self.pop_unchecked() })
    }

    /// # Safety
    ///
    /// Make sure that length is non-zero
    #[inline]
    pub fn pop_unchecked(&mut self) -> T {
        self.len -= 1;
        unsafe { ptr::read(self.buf.add(self.len)) }
    }
}

impl<T: fmt::Display> fmt::Display for Stack<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[")?;
        for i in 0..self.len {
            // Safety: The index is in bounds since it's less than self.len
            write!(f, "{}", unsafe { self.get_unchecked(i) })?;
            if i < self.len - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")
    }
}

impl<T> Drop for Stack<T> {
    fn drop(&mut self) {
        Self::dealloc_old_buf(self.buf, self.layout);
    }
}

impl<T> Clone for Stack<T> {
    fn clone(&self) -> Self {
        let buf = Self::alloc_new_buf(self.layout);
        // Safety: self.buf and buf are guaranteed to be valid and have space for self.len elements
        unsafe { ptr::copy(self.buf, buf, self.len); };

        Self {
            len: self.len,
            cap: self.cap,
            buf,
            layout: self.layout,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_new() {
        let stack: Stack<i32> = Stack::new();
        assert_eq!(stack.len(), 0);
        assert_eq!(stack.cap(), 2);
        assert!(stack.is_empty());
    }

    #[test]
    fn test_stack_with_capacity() {
        let stack: Stack<i32> = Stack::with_capacity(5);
        assert_eq!(stack.len(), 0);
        assert_eq!(stack.cap(), 5);
        assert!(stack.is_empty());
    }

    #[test]
    #[should_panic(expected = "The capacity must not be 0")]
    fn test_stack_with_capacity_zero() {
        Stack::<i32>::with_capacity(0);
    }

    #[test]
    fn test_stack_push() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.len(), 2);
        assert!(!stack.is_empty());
        assert_eq!(stack.peek(), Some(&2));
    }

    #[test]
    fn test_stack_pop() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.pop(), Some(2));
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.pop(), Some(1));
        assert!(stack.is_empty());
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn test_stack_peek() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(stack.peek(), Some(&2));
        stack.pop();
        assert_eq!(stack.peek(), Some(&1));
        stack.pop();
        assert_eq!(stack.peek(), None);
    }

    #[test]
    fn test_stack_clone() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        let cloned_stack = stack.clone();
        assert_eq!(cloned_stack.len(), 2);
        assert_eq!(cloned_stack.peek(), Some(&2));

        // Ensure changes in the original stack do not affect the clone
        stack.push(3);
        assert_eq!(stack.len(), 3);
        assert_eq!(cloned_stack.len(), 2);
    }

    #[test]
    fn test_stack_clear() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        stack.clear();
        assert!(stack.is_empty());
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn test_stack_display() {
        let mut stack: Stack<i32> = Stack::new();
        stack.push(1);
        stack.push(2);
        assert_eq!(format!("{}", stack), "[1, 2]");
    }
}
