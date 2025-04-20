use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn, Ident};

/// Trap handler ASM trampoline to the Rust impl
fn gen_trap_save_and_call(impl_fn_name: &Ident) -> proc_macro2::TokenStream {
    quote! {
        core::arch::naked_asm!(
            "addi sp, sp, -128",
            "sd ra, 0(sp)",
            "sd t0, 8(sp)",
            "sd t1, 16(sp)",
            "sd t2, 24(sp)",
            "sd t3, 32(sp)",
            "sd t4, 40(sp)",
            "sd t5, 48(sp)",
            "sd t6, 56(sp)",
            "sd a0, 64(sp)",
            "sd a1, 72(sp)",
            "sd a2, 80(sp)",
            "sd a3, 88(sp)",
            "sd a4, 96(sp)",
            "sd a5, 104(sp)",
            "sd a6, 112(sp)",
            "sd a7, 120(sp)",
            "lla a0, {trap_handler}",
            "jalr a0",
            "ld ra, 0(sp)",
            "ld t0, 8(sp)",
            "ld t1, 16(sp)",
            "ld t2, 24(sp)",
            "ld t3, 32(sp)",
            "ld t4, 40(sp)",
            "ld t5, 48(sp)",
            "ld t6, 56(sp)",
            "ld a0, 64(sp)",
            "ld a1, 72(sp)",
            "ld a2, 80(sp)",
            "ld a3, 88(sp)",
            "ld a4, 96(sp)",
            "ld a5, 104(sp)",
            "ld a6, 112(sp)",
            "ld a7, 120(sp)",
            "addi sp, sp, 128",
            "mret",
            trap_handler = sym #impl_fn_name
        )
    }
}

#[proc_macro_attribute]
pub fn trap_handler(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);

    let outer_name = input_fn.sig.ident.clone();
    let inner_name = Ident::new(&format!("{}_impl", outer_name), outer_name.span());
    let body = input_fn.block;
    let vis = input_fn.vis.clone();

    let asm_body = gen_trap_save_and_call(&inner_name);
    let expanded = quote! {
        #[unsafe(no_mangle)]
        #[unsafe(link_section = ".trap_handler")]
        #vis unsafe extern "C" fn #inner_name() #body

        #[unsafe(no_mangle)]
        #[unsafe(naked)]
        #[unsafe(link_section = ".trap_handler")]
        pub unsafe extern "C" fn #outer_name() {
            #asm_body
        }
    };

    expanded.into()
}
