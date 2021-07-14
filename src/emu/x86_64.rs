macro_rules! gen_asm {
    ($ops:ident $($t:tt)*) => {
        dynasm!($ops
            ; .arch x64

            $($t)*
        )
    }
}