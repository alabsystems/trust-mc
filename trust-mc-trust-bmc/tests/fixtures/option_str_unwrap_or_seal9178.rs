#![crate_type = "lib"]

pub fn extract_method_name(path: &str) -> Option<&str> {
    let raw = if let Some((_, suffix)) = path.rsplit_once(">::") {
        suffix
    } else if let Some((_, suffix)) = path.rsplit_once("::") {
        suffix
    } else {
        return None;
    };
    Some(raw.split("::<").next().unwrap_or(raw))
}

pub fn lookup_pattern_trait(path: &str) -> Option<u8> {
    match extract_method_name(path) {
        Some("is_contained_in") => Some(1),
        Some("is_prefix_of") => Some(2),
        Some("is_suffix_of") => Some(3),
        _ => None,
    }
}

pub const HANDLER: fn(&str) -> Option<u8> = |path| lookup_pattern_trait(path);
