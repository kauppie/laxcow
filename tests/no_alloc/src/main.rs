//! Purpose of this test is to ensure that `laxcow` can be compiled
//! on `no_std` targets without `alloc` feature enabled.

#![no_std]
#![no_main]
use core::panic::PanicInfo;

#[panic_handler]
fn panic(_info: &PanicInfo) -> ! {
    loop {}
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    loop {
        // Do something with LaxCow which doesn't depend on `alloc`.
        // This doesn't need to test anything, just ensure that `laxcow` compiles.
        let mut lax = laxcow::LaxCow::<_, ()>::Borrowed("Hello, world!");
        let _ = lax.try_as_owned_mut();
    }
}
