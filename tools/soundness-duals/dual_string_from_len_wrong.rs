// Guards the StringFrom fld_len pinning (codegen_call_string.rs): String::from(literal)
// pins the flattened fld_len to the EXACT source byte length. "Mark" has len 4, so
// asserting len()==5 (or >4) MUST FAIL (Genuine) — proves the fix pins the length to
// the TRUE value (not force-true / not a dropped check). A SUCCESSFUL here would mean
// the length was left unconstrained or wrongly pinned.
#[kani::proof]
fn dual_string_from_len_wrong() {
    let name = String::from("Mark");
    let s = name.as_str();
    assert!(s.len() == 5);
}
