
// Debugging

static mut INDENT: usize = 0;

#[allow(dead_code)]
pub fn indent() -> String {
    unsafe {
        " ".repeat(INDENT * 4)
    }
}

#[allow(dead_code)]
pub fn more_indent() -> String {
    unsafe {
        INDENT += 1;
        " ".repeat(INDENT * 4)
    }
}

#[allow(dead_code)]
pub fn less_indent() -> String {
    unsafe {
        INDENT -= 1;
        " ".repeat(INDENT * 4)
    }
}

