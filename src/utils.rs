
// Debugging

static mut INDENT: usize = 0;

#[allow(dead_code)]
pub fn indent() -> String {
    unsafe {
        std::iter::repeat(' ').take(INDENT * 4).collect::<String>()
    }
}

#[allow(dead_code)]
pub fn more_indent() -> String {
    unsafe {
        INDENT += 1;
        std::iter::repeat(' ').take(INDENT * 4).collect::<String>()
    }
}

#[allow(dead_code)]
pub fn less_indent() -> String {
    unsafe {
        INDENT -= 1;
        std::iter::repeat(' ').take(INDENT * 4).collect::<String>()
    }
}

