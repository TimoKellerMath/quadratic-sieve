use colored_text::Colorize;

pub fn format_color(string: &str, index_thread: usize) -> String {
    const COLOR_TABLE: [(u8, u8, u8); 16] = [
        (128, 0, 0),
        (255, 0, 0),
        (0, 128, 0),
        (128, 128, 0),
        (128, 255, 0),
        (255, 255, 0),
        (0, 0, 128),
        (0, 128, 128),
        (128, 128, 128),
        (255, 128, 128),
        (255, 255, 128),
        (255, 128, 255),
        (128, 128, 255),
        (0, 128, 255),
        (255, 255, 255),
        (64, 64, 64),
    ];
    string.rgb(
        COLOR_TABLE[index_thread % COLOR_TABLE.len()].0,
        COLOR_TABLE[index_thread % COLOR_TABLE.len()].1,
        COLOR_TABLE[index_thread % COLOR_TABLE.len()].2,
    )
}
