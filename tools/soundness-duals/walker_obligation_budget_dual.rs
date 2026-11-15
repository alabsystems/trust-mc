// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SOUNDNESS DUAL (both directions) -- a local callee the CHC inline walker
//! havocs, whose obligation lies past the obligation walk's budget (256
//! bodies).
//!
//! Oracle (per harness, the corpus-rev Kani 4c0fce8c3, measured 2026-09-27):
//!   bug_obligation_past_budget_multi       -> VERIFICATION:- FAILED  ("past the budget")
//!   safe_obligation_free_past_budget_multi -> VERIFICATION:- SUCCESSFUL
//!   bug_obligation_before_budget_multi     -> VERIFICATION:- FAILED  ("past the budget"; control)
//!
//! MECHANISM UNDER TEST. `big_*` make 300 obligation-free calls, too many
//! blocks for the walker, so the nested-call fallback havocs the call under
//! the blessed `nested_call_overapprox`, and keeps the blessing unless the
//! obligation walk SIGHTS an obligation in the callee
//! (`obligation_free_walk::body_has_visible_obligation`). That walk reads 256
//! bodies before it gives up, and giving up answered "could not tell", which
//! kept the blessing: `inner_bug`'s assertion sits past the budget, and on
//! main c22e1022e bug_obligation_past_budget_multi verified SUCCESSFUL clean.
//! FIXED in the package round of fix/chc-walker-fail-closed (item b): a walk
//! that runs out of budget counts as a sighting (the unread code may hold the
//! obligation), so the havoc fails closed (`nested_call_dropped_obligation`).
//! The control's obligation is sighted before the budget on both bundles. The
//! safe row is the rule's precision cost: its 300 bodies are obligation-free,
//! but the walk cannot know that within its budget, so it fails closed too
//! (known-red false failure).
//!
//! Lane scope: CHC only.
//!
//! Run: trust-mc-driver --ay-chc -Z unstable-options --harness-timeout=30s walker_obligation_budget_dual.rs

#[inline(never)]
fn sink<T>(_value: T) {}

pub struct Other;

#[inline(never)] fn f1(x: u8) -> u8 { x ^ 1 }
#[inline(never)] fn f2(x: u8) -> u8 { x ^ 2 }
#[inline(never)] fn f3(x: u8) -> u8 { x ^ 3 }
#[inline(never)] fn f4(x: u8) -> u8 { x ^ 4 }
#[inline(never)] fn f5(x: u8) -> u8 { x ^ 5 }
#[inline(never)] fn f6(x: u8) -> u8 { x ^ 6 }
#[inline(never)] fn f7(x: u8) -> u8 { x ^ 7 }
#[inline(never)] fn f8(x: u8) -> u8 { x ^ 8 }
#[inline(never)] fn f9(x: u8) -> u8 { x ^ 9 }
#[inline(never)] fn f10(x: u8) -> u8 { x ^ 10 }
#[inline(never)] fn f11(x: u8) -> u8 { x ^ 11 }
#[inline(never)] fn f12(x: u8) -> u8 { x ^ 12 }
#[inline(never)] fn f13(x: u8) -> u8 { x ^ 13 }
#[inline(never)] fn f14(x: u8) -> u8 { x ^ 14 }
#[inline(never)] fn f15(x: u8) -> u8 { x ^ 15 }
#[inline(never)] fn f16(x: u8) -> u8 { x ^ 16 }
#[inline(never)] fn f17(x: u8) -> u8 { x ^ 17 }
#[inline(never)] fn f18(x: u8) -> u8 { x ^ 18 }
#[inline(never)] fn f19(x: u8) -> u8 { x ^ 19 }
#[inline(never)] fn f20(x: u8) -> u8 { x ^ 20 }
#[inline(never)] fn f21(x: u8) -> u8 { x ^ 21 }
#[inline(never)] fn f22(x: u8) -> u8 { x ^ 22 }
#[inline(never)] fn f23(x: u8) -> u8 { x ^ 23 }
#[inline(never)] fn f24(x: u8) -> u8 { x ^ 24 }
#[inline(never)] fn f25(x: u8) -> u8 { x ^ 25 }
#[inline(never)] fn f26(x: u8) -> u8 { x ^ 26 }
#[inline(never)] fn f27(x: u8) -> u8 { x ^ 27 }
#[inline(never)] fn f28(x: u8) -> u8 { x ^ 28 }
#[inline(never)] fn f29(x: u8) -> u8 { x ^ 29 }
#[inline(never)] fn f30(x: u8) -> u8 { x ^ 30 }
#[inline(never)] fn f31(x: u8) -> u8 { x ^ 31 }
#[inline(never)] fn f32(x: u8) -> u8 { x ^ 32 }
#[inline(never)] fn f33(x: u8) -> u8 { x ^ 33 }
#[inline(never)] fn f34(x: u8) -> u8 { x ^ 34 }
#[inline(never)] fn f35(x: u8) -> u8 { x ^ 35 }
#[inline(never)] fn f36(x: u8) -> u8 { x ^ 36 }
#[inline(never)] fn f37(x: u8) -> u8 { x ^ 37 }
#[inline(never)] fn f38(x: u8) -> u8 { x ^ 38 }
#[inline(never)] fn f39(x: u8) -> u8 { x ^ 39 }
#[inline(never)] fn f40(x: u8) -> u8 { x ^ 40 }
#[inline(never)] fn f41(x: u8) -> u8 { x ^ 41 }
#[inline(never)] fn f42(x: u8) -> u8 { x ^ 42 }
#[inline(never)] fn f43(x: u8) -> u8 { x ^ 43 }
#[inline(never)] fn f44(x: u8) -> u8 { x ^ 44 }
#[inline(never)] fn f45(x: u8) -> u8 { x ^ 45 }
#[inline(never)] fn f46(x: u8) -> u8 { x ^ 46 }
#[inline(never)] fn f47(x: u8) -> u8 { x ^ 47 }
#[inline(never)] fn f48(x: u8) -> u8 { x ^ 48 }
#[inline(never)] fn f49(x: u8) -> u8 { x ^ 49 }
#[inline(never)] fn f50(x: u8) -> u8 { x ^ 50 }
#[inline(never)] fn f51(x: u8) -> u8 { x ^ 51 }
#[inline(never)] fn f52(x: u8) -> u8 { x ^ 52 }
#[inline(never)] fn f53(x: u8) -> u8 { x ^ 53 }
#[inline(never)] fn f54(x: u8) -> u8 { x ^ 54 }
#[inline(never)] fn f55(x: u8) -> u8 { x ^ 55 }
#[inline(never)] fn f56(x: u8) -> u8 { x ^ 56 }
#[inline(never)] fn f57(x: u8) -> u8 { x ^ 57 }
#[inline(never)] fn f58(x: u8) -> u8 { x ^ 58 }
#[inline(never)] fn f59(x: u8) -> u8 { x ^ 59 }
#[inline(never)] fn f60(x: u8) -> u8 { x ^ 60 }
#[inline(never)] fn f61(x: u8) -> u8 { x ^ 61 }
#[inline(never)] fn f62(x: u8) -> u8 { x ^ 62 }
#[inline(never)] fn f63(x: u8) -> u8 { x ^ 63 }
#[inline(never)] fn f64(x: u8) -> u8 { x ^ 64 }
#[inline(never)] fn f65(x: u8) -> u8 { x ^ 65 }
#[inline(never)] fn f66(x: u8) -> u8 { x ^ 66 }
#[inline(never)] fn f67(x: u8) -> u8 { x ^ 67 }
#[inline(never)] fn f68(x: u8) -> u8 { x ^ 68 }
#[inline(never)] fn f69(x: u8) -> u8 { x ^ 69 }
#[inline(never)] fn f70(x: u8) -> u8 { x ^ 70 }
#[inline(never)] fn f71(x: u8) -> u8 { x ^ 71 }
#[inline(never)] fn f72(x: u8) -> u8 { x ^ 72 }
#[inline(never)] fn f73(x: u8) -> u8 { x ^ 73 }
#[inline(never)] fn f74(x: u8) -> u8 { x ^ 74 }
#[inline(never)] fn f75(x: u8) -> u8 { x ^ 75 }
#[inline(never)] fn f76(x: u8) -> u8 { x ^ 76 }
#[inline(never)] fn f77(x: u8) -> u8 { x ^ 77 }
#[inline(never)] fn f78(x: u8) -> u8 { x ^ 78 }
#[inline(never)] fn f79(x: u8) -> u8 { x ^ 79 }
#[inline(never)] fn f80(x: u8) -> u8 { x ^ 80 }
#[inline(never)] fn f81(x: u8) -> u8 { x ^ 81 }
#[inline(never)] fn f82(x: u8) -> u8 { x ^ 82 }
#[inline(never)] fn f83(x: u8) -> u8 { x ^ 83 }
#[inline(never)] fn f84(x: u8) -> u8 { x ^ 84 }
#[inline(never)] fn f85(x: u8) -> u8 { x ^ 85 }
#[inline(never)] fn f86(x: u8) -> u8 { x ^ 86 }
#[inline(never)] fn f87(x: u8) -> u8 { x ^ 87 }
#[inline(never)] fn f88(x: u8) -> u8 { x ^ 88 }
#[inline(never)] fn f89(x: u8) -> u8 { x ^ 89 }
#[inline(never)] fn f90(x: u8) -> u8 { x ^ 90 }
#[inline(never)] fn f91(x: u8) -> u8 { x ^ 91 }
#[inline(never)] fn f92(x: u8) -> u8 { x ^ 92 }
#[inline(never)] fn f93(x: u8) -> u8 { x ^ 93 }
#[inline(never)] fn f94(x: u8) -> u8 { x ^ 94 }
#[inline(never)] fn f95(x: u8) -> u8 { x ^ 95 }
#[inline(never)] fn f96(x: u8) -> u8 { x ^ 96 }
#[inline(never)] fn f97(x: u8) -> u8 { x ^ 97 }
#[inline(never)] fn f98(x: u8) -> u8 { x ^ 98 }
#[inline(never)] fn f99(x: u8) -> u8 { x ^ 99 }
#[inline(never)] fn f100(x: u8) -> u8 { x ^ 100 }
#[inline(never)] fn f101(x: u8) -> u8 { x ^ 101 }
#[inline(never)] fn f102(x: u8) -> u8 { x ^ 102 }
#[inline(never)] fn f103(x: u8) -> u8 { x ^ 103 }
#[inline(never)] fn f104(x: u8) -> u8 { x ^ 104 }
#[inline(never)] fn f105(x: u8) -> u8 { x ^ 105 }
#[inline(never)] fn f106(x: u8) -> u8 { x ^ 106 }
#[inline(never)] fn f107(x: u8) -> u8 { x ^ 107 }
#[inline(never)] fn f108(x: u8) -> u8 { x ^ 108 }
#[inline(never)] fn f109(x: u8) -> u8 { x ^ 109 }
#[inline(never)] fn f110(x: u8) -> u8 { x ^ 110 }
#[inline(never)] fn f111(x: u8) -> u8 { x ^ 111 }
#[inline(never)] fn f112(x: u8) -> u8 { x ^ 112 }
#[inline(never)] fn f113(x: u8) -> u8 { x ^ 113 }
#[inline(never)] fn f114(x: u8) -> u8 { x ^ 114 }
#[inline(never)] fn f115(x: u8) -> u8 { x ^ 115 }
#[inline(never)] fn f116(x: u8) -> u8 { x ^ 116 }
#[inline(never)] fn f117(x: u8) -> u8 { x ^ 117 }
#[inline(never)] fn f118(x: u8) -> u8 { x ^ 118 }
#[inline(never)] fn f119(x: u8) -> u8 { x ^ 119 }
#[inline(never)] fn f120(x: u8) -> u8 { x ^ 120 }
#[inline(never)] fn f121(x: u8) -> u8 { x ^ 121 }
#[inline(never)] fn f122(x: u8) -> u8 { x ^ 122 }
#[inline(never)] fn f123(x: u8) -> u8 { x ^ 123 }
#[inline(never)] fn f124(x: u8) -> u8 { x ^ 124 }
#[inline(never)] fn f125(x: u8) -> u8 { x ^ 125 }
#[inline(never)] fn f126(x: u8) -> u8 { x ^ 126 }
#[inline(never)] fn f127(x: u8) -> u8 { x ^ 127 }
#[inline(never)] fn f128(x: u8) -> u8 { x ^ 128 }
#[inline(never)] fn f129(x: u8) -> u8 { x ^ 129 }
#[inline(never)] fn f130(x: u8) -> u8 { x ^ 130 }
#[inline(never)] fn f131(x: u8) -> u8 { x ^ 131 }
#[inline(never)] fn f132(x: u8) -> u8 { x ^ 132 }
#[inline(never)] fn f133(x: u8) -> u8 { x ^ 133 }
#[inline(never)] fn f134(x: u8) -> u8 { x ^ 134 }
#[inline(never)] fn f135(x: u8) -> u8 { x ^ 135 }
#[inline(never)] fn f136(x: u8) -> u8 { x ^ 136 }
#[inline(never)] fn f137(x: u8) -> u8 { x ^ 137 }
#[inline(never)] fn f138(x: u8) -> u8 { x ^ 138 }
#[inline(never)] fn f139(x: u8) -> u8 { x ^ 139 }
#[inline(never)] fn f140(x: u8) -> u8 { x ^ 140 }
#[inline(never)] fn f141(x: u8) -> u8 { x ^ 141 }
#[inline(never)] fn f142(x: u8) -> u8 { x ^ 142 }
#[inline(never)] fn f143(x: u8) -> u8 { x ^ 143 }
#[inline(never)] fn f144(x: u8) -> u8 { x ^ 144 }
#[inline(never)] fn f145(x: u8) -> u8 { x ^ 145 }
#[inline(never)] fn f146(x: u8) -> u8 { x ^ 146 }
#[inline(never)] fn f147(x: u8) -> u8 { x ^ 147 }
#[inline(never)] fn f148(x: u8) -> u8 { x ^ 148 }
#[inline(never)] fn f149(x: u8) -> u8 { x ^ 149 }
#[inline(never)] fn f150(x: u8) -> u8 { x ^ 150 }
#[inline(never)] fn f151(x: u8) -> u8 { x ^ 151 }
#[inline(never)] fn f152(x: u8) -> u8 { x ^ 152 }
#[inline(never)] fn f153(x: u8) -> u8 { x ^ 153 }
#[inline(never)] fn f154(x: u8) -> u8 { x ^ 154 }
#[inline(never)] fn f155(x: u8) -> u8 { x ^ 155 }
#[inline(never)] fn f156(x: u8) -> u8 { x ^ 156 }
#[inline(never)] fn f157(x: u8) -> u8 { x ^ 157 }
#[inline(never)] fn f158(x: u8) -> u8 { x ^ 158 }
#[inline(never)] fn f159(x: u8) -> u8 { x ^ 159 }
#[inline(never)] fn f160(x: u8) -> u8 { x ^ 160 }
#[inline(never)] fn f161(x: u8) -> u8 { x ^ 161 }
#[inline(never)] fn f162(x: u8) -> u8 { x ^ 162 }
#[inline(never)] fn f163(x: u8) -> u8 { x ^ 163 }
#[inline(never)] fn f164(x: u8) -> u8 { x ^ 164 }
#[inline(never)] fn f165(x: u8) -> u8 { x ^ 165 }
#[inline(never)] fn f166(x: u8) -> u8 { x ^ 166 }
#[inline(never)] fn f167(x: u8) -> u8 { x ^ 167 }
#[inline(never)] fn f168(x: u8) -> u8 { x ^ 168 }
#[inline(never)] fn f169(x: u8) -> u8 { x ^ 169 }
#[inline(never)] fn f170(x: u8) -> u8 { x ^ 170 }
#[inline(never)] fn f171(x: u8) -> u8 { x ^ 171 }
#[inline(never)] fn f172(x: u8) -> u8 { x ^ 172 }
#[inline(never)] fn f173(x: u8) -> u8 { x ^ 173 }
#[inline(never)] fn f174(x: u8) -> u8 { x ^ 174 }
#[inline(never)] fn f175(x: u8) -> u8 { x ^ 175 }
#[inline(never)] fn f176(x: u8) -> u8 { x ^ 176 }
#[inline(never)] fn f177(x: u8) -> u8 { x ^ 177 }
#[inline(never)] fn f178(x: u8) -> u8 { x ^ 178 }
#[inline(never)] fn f179(x: u8) -> u8 { x ^ 179 }
#[inline(never)] fn f180(x: u8) -> u8 { x ^ 180 }
#[inline(never)] fn f181(x: u8) -> u8 { x ^ 181 }
#[inline(never)] fn f182(x: u8) -> u8 { x ^ 182 }
#[inline(never)] fn f183(x: u8) -> u8 { x ^ 183 }
#[inline(never)] fn f184(x: u8) -> u8 { x ^ 184 }
#[inline(never)] fn f185(x: u8) -> u8 { x ^ 185 }
#[inline(never)] fn f186(x: u8) -> u8 { x ^ 186 }
#[inline(never)] fn f187(x: u8) -> u8 { x ^ 187 }
#[inline(never)] fn f188(x: u8) -> u8 { x ^ 188 }
#[inline(never)] fn f189(x: u8) -> u8 { x ^ 189 }
#[inline(never)] fn f190(x: u8) -> u8 { x ^ 190 }
#[inline(never)] fn f191(x: u8) -> u8 { x ^ 191 }
#[inline(never)] fn f192(x: u8) -> u8 { x ^ 192 }
#[inline(never)] fn f193(x: u8) -> u8 { x ^ 193 }
#[inline(never)] fn f194(x: u8) -> u8 { x ^ 194 }
#[inline(never)] fn f195(x: u8) -> u8 { x ^ 195 }
#[inline(never)] fn f196(x: u8) -> u8 { x ^ 196 }
#[inline(never)] fn f197(x: u8) -> u8 { x ^ 197 }
#[inline(never)] fn f198(x: u8) -> u8 { x ^ 198 }
#[inline(never)] fn f199(x: u8) -> u8 { x ^ 199 }
#[inline(never)] fn f200(x: u8) -> u8 { x ^ 200 }
#[inline(never)] fn f201(x: u8) -> u8 { x ^ 201 }
#[inline(never)] fn f202(x: u8) -> u8 { x ^ 202 }
#[inline(never)] fn f203(x: u8) -> u8 { x ^ 203 }
#[inline(never)] fn f204(x: u8) -> u8 { x ^ 204 }
#[inline(never)] fn f205(x: u8) -> u8 { x ^ 205 }
#[inline(never)] fn f206(x: u8) -> u8 { x ^ 206 }
#[inline(never)] fn f207(x: u8) -> u8 { x ^ 207 }
#[inline(never)] fn f208(x: u8) -> u8 { x ^ 208 }
#[inline(never)] fn f209(x: u8) -> u8 { x ^ 209 }
#[inline(never)] fn f210(x: u8) -> u8 { x ^ 210 }
#[inline(never)] fn f211(x: u8) -> u8 { x ^ 211 }
#[inline(never)] fn f212(x: u8) -> u8 { x ^ 212 }
#[inline(never)] fn f213(x: u8) -> u8 { x ^ 213 }
#[inline(never)] fn f214(x: u8) -> u8 { x ^ 214 }
#[inline(never)] fn f215(x: u8) -> u8 { x ^ 215 }
#[inline(never)] fn f216(x: u8) -> u8 { x ^ 216 }
#[inline(never)] fn f217(x: u8) -> u8 { x ^ 217 }
#[inline(never)] fn f218(x: u8) -> u8 { x ^ 218 }
#[inline(never)] fn f219(x: u8) -> u8 { x ^ 219 }
#[inline(never)] fn f220(x: u8) -> u8 { x ^ 220 }
#[inline(never)] fn f221(x: u8) -> u8 { x ^ 221 }
#[inline(never)] fn f222(x: u8) -> u8 { x ^ 222 }
#[inline(never)] fn f223(x: u8) -> u8 { x ^ 223 }
#[inline(never)] fn f224(x: u8) -> u8 { x ^ 224 }
#[inline(never)] fn f225(x: u8) -> u8 { x ^ 225 }
#[inline(never)] fn f226(x: u8) -> u8 { x ^ 226 }
#[inline(never)] fn f227(x: u8) -> u8 { x ^ 227 }
#[inline(never)] fn f228(x: u8) -> u8 { x ^ 228 }
#[inline(never)] fn f229(x: u8) -> u8 { x ^ 229 }
#[inline(never)] fn f230(x: u8) -> u8 { x ^ 230 }
#[inline(never)] fn f231(x: u8) -> u8 { x ^ 231 }
#[inline(never)] fn f232(x: u8) -> u8 { x ^ 232 }
#[inline(never)] fn f233(x: u8) -> u8 { x ^ 233 }
#[inline(never)] fn f234(x: u8) -> u8 { x ^ 234 }
#[inline(never)] fn f235(x: u8) -> u8 { x ^ 235 }
#[inline(never)] fn f236(x: u8) -> u8 { x ^ 236 }
#[inline(never)] fn f237(x: u8) -> u8 { x ^ 237 }
#[inline(never)] fn f238(x: u8) -> u8 { x ^ 238 }
#[inline(never)] fn f239(x: u8) -> u8 { x ^ 239 }
#[inline(never)] fn f240(x: u8) -> u8 { x ^ 240 }
#[inline(never)] fn f241(x: u8) -> u8 { x ^ 241 }
#[inline(never)] fn f242(x: u8) -> u8 { x ^ 242 }
#[inline(never)] fn f243(x: u8) -> u8 { x ^ 243 }
#[inline(never)] fn f244(x: u8) -> u8 { x ^ 244 }
#[inline(never)] fn f245(x: u8) -> u8 { x ^ 245 }
#[inline(never)] fn f246(x: u8) -> u8 { x ^ 246 }
#[inline(never)] fn f247(x: u8) -> u8 { x ^ 247 }
#[inline(never)] fn f248(x: u8) -> u8 { x ^ 248 }
#[inline(never)] fn f249(x: u8) -> u8 { x ^ 249 }
#[inline(never)] fn f250(x: u8) -> u8 { x ^ 250 }
#[inline(never)] fn f251(x: u8) -> u8 { x ^ 0 }
#[inline(never)] fn f252(x: u8) -> u8 { x ^ 1 }
#[inline(never)] fn f253(x: u8) -> u8 { x ^ 2 }
#[inline(never)] fn f254(x: u8) -> u8 { x ^ 3 }
#[inline(never)] fn f255(x: u8) -> u8 { x ^ 4 }
#[inline(never)] fn f256(x: u8) -> u8 { x ^ 5 }
#[inline(never)] fn f257(x: u8) -> u8 { x ^ 6 }
#[inline(never)] fn f258(x: u8) -> u8 { x ^ 7 }
#[inline(never)] fn f259(x: u8) -> u8 { x ^ 8 }
#[inline(never)] fn f260(x: u8) -> u8 { x ^ 9 }
#[inline(never)] fn f261(x: u8) -> u8 { x ^ 10 }
#[inline(never)] fn f262(x: u8) -> u8 { x ^ 11 }
#[inline(never)] fn f263(x: u8) -> u8 { x ^ 12 }
#[inline(never)] fn f264(x: u8) -> u8 { x ^ 13 }
#[inline(never)] fn f265(x: u8) -> u8 { x ^ 14 }
#[inline(never)] fn f266(x: u8) -> u8 { x ^ 15 }
#[inline(never)] fn f267(x: u8) -> u8 { x ^ 16 }
#[inline(never)] fn f268(x: u8) -> u8 { x ^ 17 }
#[inline(never)] fn f269(x: u8) -> u8 { x ^ 18 }
#[inline(never)] fn f270(x: u8) -> u8 { x ^ 19 }
#[inline(never)] fn f271(x: u8) -> u8 { x ^ 20 }
#[inline(never)] fn f272(x: u8) -> u8 { x ^ 21 }
#[inline(never)] fn f273(x: u8) -> u8 { x ^ 22 }
#[inline(never)] fn f274(x: u8) -> u8 { x ^ 23 }
#[inline(never)] fn f275(x: u8) -> u8 { x ^ 24 }
#[inline(never)] fn f276(x: u8) -> u8 { x ^ 25 }
#[inline(never)] fn f277(x: u8) -> u8 { x ^ 26 }
#[inline(never)] fn f278(x: u8) -> u8 { x ^ 27 }
#[inline(never)] fn f279(x: u8) -> u8 { x ^ 28 }
#[inline(never)] fn f280(x: u8) -> u8 { x ^ 29 }
#[inline(never)] fn f281(x: u8) -> u8 { x ^ 30 }
#[inline(never)] fn f282(x: u8) -> u8 { x ^ 31 }
#[inline(never)] fn f283(x: u8) -> u8 { x ^ 32 }
#[inline(never)] fn f284(x: u8) -> u8 { x ^ 33 }
#[inline(never)] fn f285(x: u8) -> u8 { x ^ 34 }
#[inline(never)] fn f286(x: u8) -> u8 { x ^ 35 }
#[inline(never)] fn f287(x: u8) -> u8 { x ^ 36 }
#[inline(never)] fn f288(x: u8) -> u8 { x ^ 37 }
#[inline(never)] fn f289(x: u8) -> u8 { x ^ 38 }
#[inline(never)] fn f290(x: u8) -> u8 { x ^ 39 }
#[inline(never)] fn f291(x: u8) -> u8 { x ^ 40 }
#[inline(never)] fn f292(x: u8) -> u8 { x ^ 41 }
#[inline(never)] fn f293(x: u8) -> u8 { x ^ 42 }
#[inline(never)] fn f294(x: u8) -> u8 { x ^ 43 }
#[inline(never)] fn f295(x: u8) -> u8 { x ^ 44 }
#[inline(never)] fn f296(x: u8) -> u8 { x ^ 45 }
#[inline(never)] fn f297(x: u8) -> u8 { x ^ 46 }
#[inline(never)] fn f298(x: u8) -> u8 { x ^ 47 }
#[inline(never)] fn f299(x: u8) -> u8 { x ^ 48 }
#[inline(never)] fn f300(x: u8) -> u8 { x ^ 49 }
#[inline(never)]
fn inner_bug(v: u8) -> u8 {
    assert!(v != 100, "past the budget");
    v
}

#[inline(never)]
fn inner_safe(v: u8) -> u8 {
    v
}

// 300 obligation-free calls, then the call that holds the obligation.
#[inline(never)]
fn big_bug(a: u8) -> u8 {
    let x = a;
    let x = f1(x);
    let x = f2(x);
    let x = f3(x);
    let x = f4(x);
    let x = f5(x);
    let x = f6(x);
    let x = f7(x);
    let x = f8(x);
    let x = f9(x);
    let x = f10(x);
    let x = f11(x);
    let x = f12(x);
    let x = f13(x);
    let x = f14(x);
    let x = f15(x);
    let x = f16(x);
    let x = f17(x);
    let x = f18(x);
    let x = f19(x);
    let x = f20(x);
    let x = f21(x);
    let x = f22(x);
    let x = f23(x);
    let x = f24(x);
    let x = f25(x);
    let x = f26(x);
    let x = f27(x);
    let x = f28(x);
    let x = f29(x);
    let x = f30(x);
    let x = f31(x);
    let x = f32(x);
    let x = f33(x);
    let x = f34(x);
    let x = f35(x);
    let x = f36(x);
    let x = f37(x);
    let x = f38(x);
    let x = f39(x);
    let x = f40(x);
    let x = f41(x);
    let x = f42(x);
    let x = f43(x);
    let x = f44(x);
    let x = f45(x);
    let x = f46(x);
    let x = f47(x);
    let x = f48(x);
    let x = f49(x);
    let x = f50(x);
    let x = f51(x);
    let x = f52(x);
    let x = f53(x);
    let x = f54(x);
    let x = f55(x);
    let x = f56(x);
    let x = f57(x);
    let x = f58(x);
    let x = f59(x);
    let x = f60(x);
    let x = f61(x);
    let x = f62(x);
    let x = f63(x);
    let x = f64(x);
    let x = f65(x);
    let x = f66(x);
    let x = f67(x);
    let x = f68(x);
    let x = f69(x);
    let x = f70(x);
    let x = f71(x);
    let x = f72(x);
    let x = f73(x);
    let x = f74(x);
    let x = f75(x);
    let x = f76(x);
    let x = f77(x);
    let x = f78(x);
    let x = f79(x);
    let x = f80(x);
    let x = f81(x);
    let x = f82(x);
    let x = f83(x);
    let x = f84(x);
    let x = f85(x);
    let x = f86(x);
    let x = f87(x);
    let x = f88(x);
    let x = f89(x);
    let x = f90(x);
    let x = f91(x);
    let x = f92(x);
    let x = f93(x);
    let x = f94(x);
    let x = f95(x);
    let x = f96(x);
    let x = f97(x);
    let x = f98(x);
    let x = f99(x);
    let x = f100(x);
    let x = f101(x);
    let x = f102(x);
    let x = f103(x);
    let x = f104(x);
    let x = f105(x);
    let x = f106(x);
    let x = f107(x);
    let x = f108(x);
    let x = f109(x);
    let x = f110(x);
    let x = f111(x);
    let x = f112(x);
    let x = f113(x);
    let x = f114(x);
    let x = f115(x);
    let x = f116(x);
    let x = f117(x);
    let x = f118(x);
    let x = f119(x);
    let x = f120(x);
    let x = f121(x);
    let x = f122(x);
    let x = f123(x);
    let x = f124(x);
    let x = f125(x);
    let x = f126(x);
    let x = f127(x);
    let x = f128(x);
    let x = f129(x);
    let x = f130(x);
    let x = f131(x);
    let x = f132(x);
    let x = f133(x);
    let x = f134(x);
    let x = f135(x);
    let x = f136(x);
    let x = f137(x);
    let x = f138(x);
    let x = f139(x);
    let x = f140(x);
    let x = f141(x);
    let x = f142(x);
    let x = f143(x);
    let x = f144(x);
    let x = f145(x);
    let x = f146(x);
    let x = f147(x);
    let x = f148(x);
    let x = f149(x);
    let x = f150(x);
    let x = f151(x);
    let x = f152(x);
    let x = f153(x);
    let x = f154(x);
    let x = f155(x);
    let x = f156(x);
    let x = f157(x);
    let x = f158(x);
    let x = f159(x);
    let x = f160(x);
    let x = f161(x);
    let x = f162(x);
    let x = f163(x);
    let x = f164(x);
    let x = f165(x);
    let x = f166(x);
    let x = f167(x);
    let x = f168(x);
    let x = f169(x);
    let x = f170(x);
    let x = f171(x);
    let x = f172(x);
    let x = f173(x);
    let x = f174(x);
    let x = f175(x);
    let x = f176(x);
    let x = f177(x);
    let x = f178(x);
    let x = f179(x);
    let x = f180(x);
    let x = f181(x);
    let x = f182(x);
    let x = f183(x);
    let x = f184(x);
    let x = f185(x);
    let x = f186(x);
    let x = f187(x);
    let x = f188(x);
    let x = f189(x);
    let x = f190(x);
    let x = f191(x);
    let x = f192(x);
    let x = f193(x);
    let x = f194(x);
    let x = f195(x);
    let x = f196(x);
    let x = f197(x);
    let x = f198(x);
    let x = f199(x);
    let x = f200(x);
    let x = f201(x);
    let x = f202(x);
    let x = f203(x);
    let x = f204(x);
    let x = f205(x);
    let x = f206(x);
    let x = f207(x);
    let x = f208(x);
    let x = f209(x);
    let x = f210(x);
    let x = f211(x);
    let x = f212(x);
    let x = f213(x);
    let x = f214(x);
    let x = f215(x);
    let x = f216(x);
    let x = f217(x);
    let x = f218(x);
    let x = f219(x);
    let x = f220(x);
    let x = f221(x);
    let x = f222(x);
    let x = f223(x);
    let x = f224(x);
    let x = f225(x);
    let x = f226(x);
    let x = f227(x);
    let x = f228(x);
    let x = f229(x);
    let x = f230(x);
    let x = f231(x);
    let x = f232(x);
    let x = f233(x);
    let x = f234(x);
    let x = f235(x);
    let x = f236(x);
    let x = f237(x);
    let x = f238(x);
    let x = f239(x);
    let x = f240(x);
    let x = f241(x);
    let x = f242(x);
    let x = f243(x);
    let x = f244(x);
    let x = f245(x);
    let x = f246(x);
    let x = f247(x);
    let x = f248(x);
    let x = f249(x);
    let x = f250(x);
    let x = f251(x);
    let x = f252(x);
    let x = f253(x);
    let x = f254(x);
    let x = f255(x);
    let x = f256(x);
    let x = f257(x);
    let x = f258(x);
    let x = f259(x);
    let x = f260(x);
    let x = f261(x);
    let x = f262(x);
    let x = f263(x);
    let x = f264(x);
    let x = f265(x);
    let x = f266(x);
    let x = f267(x);
    let x = f268(x);
    let x = f269(x);
    let x = f270(x);
    let x = f271(x);
    let x = f272(x);
    let x = f273(x);
    let x = f274(x);
    let x = f275(x);
    let x = f276(x);
    let x = f277(x);
    let x = f278(x);
    let x = f279(x);
    let x = f280(x);
    let x = f281(x);
    let x = f282(x);
    let x = f283(x);
    let x = f284(x);
    let x = f285(x);
    let x = f286(x);
    let x = f287(x);
    let x = f288(x);
    let x = f289(x);
    let x = f290(x);
    let x = f291(x);
    let x = f292(x);
    let x = f293(x);
    let x = f294(x);
    let x = f295(x);
    let x = f296(x);
    let x = f297(x);
    let x = f298(x);
    let x = f299(x);
    let x = f300(x);
    let _ = x;
    inner_bug(a)
}

#[inline(never)]
fn big_safe(a: u8) -> u8 {
    let x = a;
    let x = f1(x);
    let x = f2(x);
    let x = f3(x);
    let x = f4(x);
    let x = f5(x);
    let x = f6(x);
    let x = f7(x);
    let x = f8(x);
    let x = f9(x);
    let x = f10(x);
    let x = f11(x);
    let x = f12(x);
    let x = f13(x);
    let x = f14(x);
    let x = f15(x);
    let x = f16(x);
    let x = f17(x);
    let x = f18(x);
    let x = f19(x);
    let x = f20(x);
    let x = f21(x);
    let x = f22(x);
    let x = f23(x);
    let x = f24(x);
    let x = f25(x);
    let x = f26(x);
    let x = f27(x);
    let x = f28(x);
    let x = f29(x);
    let x = f30(x);
    let x = f31(x);
    let x = f32(x);
    let x = f33(x);
    let x = f34(x);
    let x = f35(x);
    let x = f36(x);
    let x = f37(x);
    let x = f38(x);
    let x = f39(x);
    let x = f40(x);
    let x = f41(x);
    let x = f42(x);
    let x = f43(x);
    let x = f44(x);
    let x = f45(x);
    let x = f46(x);
    let x = f47(x);
    let x = f48(x);
    let x = f49(x);
    let x = f50(x);
    let x = f51(x);
    let x = f52(x);
    let x = f53(x);
    let x = f54(x);
    let x = f55(x);
    let x = f56(x);
    let x = f57(x);
    let x = f58(x);
    let x = f59(x);
    let x = f60(x);
    let x = f61(x);
    let x = f62(x);
    let x = f63(x);
    let x = f64(x);
    let x = f65(x);
    let x = f66(x);
    let x = f67(x);
    let x = f68(x);
    let x = f69(x);
    let x = f70(x);
    let x = f71(x);
    let x = f72(x);
    let x = f73(x);
    let x = f74(x);
    let x = f75(x);
    let x = f76(x);
    let x = f77(x);
    let x = f78(x);
    let x = f79(x);
    let x = f80(x);
    let x = f81(x);
    let x = f82(x);
    let x = f83(x);
    let x = f84(x);
    let x = f85(x);
    let x = f86(x);
    let x = f87(x);
    let x = f88(x);
    let x = f89(x);
    let x = f90(x);
    let x = f91(x);
    let x = f92(x);
    let x = f93(x);
    let x = f94(x);
    let x = f95(x);
    let x = f96(x);
    let x = f97(x);
    let x = f98(x);
    let x = f99(x);
    let x = f100(x);
    let x = f101(x);
    let x = f102(x);
    let x = f103(x);
    let x = f104(x);
    let x = f105(x);
    let x = f106(x);
    let x = f107(x);
    let x = f108(x);
    let x = f109(x);
    let x = f110(x);
    let x = f111(x);
    let x = f112(x);
    let x = f113(x);
    let x = f114(x);
    let x = f115(x);
    let x = f116(x);
    let x = f117(x);
    let x = f118(x);
    let x = f119(x);
    let x = f120(x);
    let x = f121(x);
    let x = f122(x);
    let x = f123(x);
    let x = f124(x);
    let x = f125(x);
    let x = f126(x);
    let x = f127(x);
    let x = f128(x);
    let x = f129(x);
    let x = f130(x);
    let x = f131(x);
    let x = f132(x);
    let x = f133(x);
    let x = f134(x);
    let x = f135(x);
    let x = f136(x);
    let x = f137(x);
    let x = f138(x);
    let x = f139(x);
    let x = f140(x);
    let x = f141(x);
    let x = f142(x);
    let x = f143(x);
    let x = f144(x);
    let x = f145(x);
    let x = f146(x);
    let x = f147(x);
    let x = f148(x);
    let x = f149(x);
    let x = f150(x);
    let x = f151(x);
    let x = f152(x);
    let x = f153(x);
    let x = f154(x);
    let x = f155(x);
    let x = f156(x);
    let x = f157(x);
    let x = f158(x);
    let x = f159(x);
    let x = f160(x);
    let x = f161(x);
    let x = f162(x);
    let x = f163(x);
    let x = f164(x);
    let x = f165(x);
    let x = f166(x);
    let x = f167(x);
    let x = f168(x);
    let x = f169(x);
    let x = f170(x);
    let x = f171(x);
    let x = f172(x);
    let x = f173(x);
    let x = f174(x);
    let x = f175(x);
    let x = f176(x);
    let x = f177(x);
    let x = f178(x);
    let x = f179(x);
    let x = f180(x);
    let x = f181(x);
    let x = f182(x);
    let x = f183(x);
    let x = f184(x);
    let x = f185(x);
    let x = f186(x);
    let x = f187(x);
    let x = f188(x);
    let x = f189(x);
    let x = f190(x);
    let x = f191(x);
    let x = f192(x);
    let x = f193(x);
    let x = f194(x);
    let x = f195(x);
    let x = f196(x);
    let x = f197(x);
    let x = f198(x);
    let x = f199(x);
    let x = f200(x);
    let x = f201(x);
    let x = f202(x);
    let x = f203(x);
    let x = f204(x);
    let x = f205(x);
    let x = f206(x);
    let x = f207(x);
    let x = f208(x);
    let x = f209(x);
    let x = f210(x);
    let x = f211(x);
    let x = f212(x);
    let x = f213(x);
    let x = f214(x);
    let x = f215(x);
    let x = f216(x);
    let x = f217(x);
    let x = f218(x);
    let x = f219(x);
    let x = f220(x);
    let x = f221(x);
    let x = f222(x);
    let x = f223(x);
    let x = f224(x);
    let x = f225(x);
    let x = f226(x);
    let x = f227(x);
    let x = f228(x);
    let x = f229(x);
    let x = f230(x);
    let x = f231(x);
    let x = f232(x);
    let x = f233(x);
    let x = f234(x);
    let x = f235(x);
    let x = f236(x);
    let x = f237(x);
    let x = f238(x);
    let x = f239(x);
    let x = f240(x);
    let x = f241(x);
    let x = f242(x);
    let x = f243(x);
    let x = f244(x);
    let x = f245(x);
    let x = f246(x);
    let x = f247(x);
    let x = f248(x);
    let x = f249(x);
    let x = f250(x);
    let x = f251(x);
    let x = f252(x);
    let x = f253(x);
    let x = f254(x);
    let x = f255(x);
    let x = f256(x);
    let x = f257(x);
    let x = f258(x);
    let x = f259(x);
    let x = f260(x);
    let x = f261(x);
    let x = f262(x);
    let x = f263(x);
    let x = f264(x);
    let x = f265(x);
    let x = f266(x);
    let x = f267(x);
    let x = f268(x);
    let x = f269(x);
    let x = f270(x);
    let x = f271(x);
    let x = f272(x);
    let x = f273(x);
    let x = f274(x);
    let x = f275(x);
    let x = f276(x);
    let x = f277(x);
    let x = f278(x);
    let x = f279(x);
    let x = f280(x);
    let x = f281(x);
    let x = f282(x);
    let x = f283(x);
    let x = f284(x);
    let x = f285(x);
    let x = f286(x);
    let x = f287(x);
    let x = f288(x);
    let x = f289(x);
    let x = f290(x);
    let x = f291(x);
    let x = f292(x);
    let x = f293(x);
    let x = f294(x);
    let x = f295(x);
    let x = f296(x);
    let x = f297(x);
    let x = f298(x);
    let x = f299(x);
    let x = f300(x);
    let _ = x;
    inner_safe(a)
}

// Control: the obligation first, sighted before the budget.
#[inline(never)]
fn big_early_bug(a: u8) -> u8 {
    let a = inner_bug(a);
    let x = a;
    let x = f1(x);
    let x = f2(x);
    let x = f3(x);
    let x = f4(x);
    let x = f5(x);
    let x = f6(x);
    let x = f7(x);
    let x = f8(x);
    let x = f9(x);
    let x = f10(x);
    let x = f11(x);
    let x = f12(x);
    let x = f13(x);
    let x = f14(x);
    let x = f15(x);
    let x = f16(x);
    let x = f17(x);
    let x = f18(x);
    let x = f19(x);
    let x = f20(x);
    let x = f21(x);
    let x = f22(x);
    let x = f23(x);
    let x = f24(x);
    let x = f25(x);
    let x = f26(x);
    let x = f27(x);
    let x = f28(x);
    let x = f29(x);
    let x = f30(x);
    let x = f31(x);
    let x = f32(x);
    let x = f33(x);
    let x = f34(x);
    let x = f35(x);
    let x = f36(x);
    let x = f37(x);
    let x = f38(x);
    let x = f39(x);
    let x = f40(x);
    let x = f41(x);
    let x = f42(x);
    let x = f43(x);
    let x = f44(x);
    let x = f45(x);
    let x = f46(x);
    let x = f47(x);
    let x = f48(x);
    let x = f49(x);
    let x = f50(x);
    let x = f51(x);
    let x = f52(x);
    let x = f53(x);
    let x = f54(x);
    let x = f55(x);
    let x = f56(x);
    let x = f57(x);
    let x = f58(x);
    let x = f59(x);
    let x = f60(x);
    let x = f61(x);
    let x = f62(x);
    let x = f63(x);
    let x = f64(x);
    let x = f65(x);
    let x = f66(x);
    let x = f67(x);
    let x = f68(x);
    let x = f69(x);
    let x = f70(x);
    let x = f71(x);
    let x = f72(x);
    let x = f73(x);
    let x = f74(x);
    let x = f75(x);
    let x = f76(x);
    let x = f77(x);
    let x = f78(x);
    let x = f79(x);
    let x = f80(x);
    let x = f81(x);
    let x = f82(x);
    let x = f83(x);
    let x = f84(x);
    let x = f85(x);
    let x = f86(x);
    let x = f87(x);
    let x = f88(x);
    let x = f89(x);
    let x = f90(x);
    let x = f91(x);
    let x = f92(x);
    let x = f93(x);
    let x = f94(x);
    let x = f95(x);
    let x = f96(x);
    let x = f97(x);
    let x = f98(x);
    let x = f99(x);
    let x = f100(x);
    let x = f101(x);
    let x = f102(x);
    let x = f103(x);
    let x = f104(x);
    let x = f105(x);
    let x = f106(x);
    let x = f107(x);
    let x = f108(x);
    let x = f109(x);
    let x = f110(x);
    let x = f111(x);
    let x = f112(x);
    let x = f113(x);
    let x = f114(x);
    let x = f115(x);
    let x = f116(x);
    let x = f117(x);
    let x = f118(x);
    let x = f119(x);
    let x = f120(x);
    let x = f121(x);
    let x = f122(x);
    let x = f123(x);
    let x = f124(x);
    let x = f125(x);
    let x = f126(x);
    let x = f127(x);
    let x = f128(x);
    let x = f129(x);
    let x = f130(x);
    let x = f131(x);
    let x = f132(x);
    let x = f133(x);
    let x = f134(x);
    let x = f135(x);
    let x = f136(x);
    let x = f137(x);
    let x = f138(x);
    let x = f139(x);
    let x = f140(x);
    let x = f141(x);
    let x = f142(x);
    let x = f143(x);
    let x = f144(x);
    let x = f145(x);
    let x = f146(x);
    let x = f147(x);
    let x = f148(x);
    let x = f149(x);
    let x = f150(x);
    let x = f151(x);
    let x = f152(x);
    let x = f153(x);
    let x = f154(x);
    let x = f155(x);
    let x = f156(x);
    let x = f157(x);
    let x = f158(x);
    let x = f159(x);
    let x = f160(x);
    let x = f161(x);
    let x = f162(x);
    let x = f163(x);
    let x = f164(x);
    let x = f165(x);
    let x = f166(x);
    let x = f167(x);
    let x = f168(x);
    let x = f169(x);
    let x = f170(x);
    let x = f171(x);
    let x = f172(x);
    let x = f173(x);
    let x = f174(x);
    let x = f175(x);
    let x = f176(x);
    let x = f177(x);
    let x = f178(x);
    let x = f179(x);
    let x = f180(x);
    let x = f181(x);
    let x = f182(x);
    let x = f183(x);
    let x = f184(x);
    let x = f185(x);
    let x = f186(x);
    let x = f187(x);
    let x = f188(x);
    let x = f189(x);
    let x = f190(x);
    let x = f191(x);
    let x = f192(x);
    let x = f193(x);
    let x = f194(x);
    let x = f195(x);
    let x = f196(x);
    let x = f197(x);
    let x = f198(x);
    let x = f199(x);
    let x = f200(x);
    let x = f201(x);
    let x = f202(x);
    let x = f203(x);
    let x = f204(x);
    let x = f205(x);
    let x = f206(x);
    let x = f207(x);
    let x = f208(x);
    let x = f209(x);
    let x = f210(x);
    let x = f211(x);
    let x = f212(x);
    let x = f213(x);
    let x = f214(x);
    let x = f215(x);
    let x = f216(x);
    let x = f217(x);
    let x = f218(x);
    let x = f219(x);
    let x = f220(x);
    let x = f221(x);
    let x = f222(x);
    let x = f223(x);
    let x = f224(x);
    let x = f225(x);
    let x = f226(x);
    let x = f227(x);
    let x = f228(x);
    let x = f229(x);
    let x = f230(x);
    let x = f231(x);
    let x = f232(x);
    let x = f233(x);
    let x = f234(x);
    let x = f235(x);
    let x = f236(x);
    let x = f237(x);
    let x = f238(x);
    let x = f239(x);
    let x = f240(x);
    let x = f241(x);
    let x = f242(x);
    let x = f243(x);
    let x = f244(x);
    let x = f245(x);
    let x = f246(x);
    let x = f247(x);
    let x = f248(x);
    let x = f249(x);
    let x = f250(x);
    let x = f251(x);
    let x = f252(x);
    let x = f253(x);
    let x = f254(x);
    let x = f255(x);
    let x = f256(x);
    let x = f257(x);
    let x = f258(x);
    let x = f259(x);
    let x = f260(x);
    let x = f261(x);
    let x = f262(x);
    let x = f263(x);
    let x = f264(x);
    let x = f265(x);
    let x = f266(x);
    let x = f267(x);
    let x = f268(x);
    let x = f269(x);
    let x = f270(x);
    let x = f271(x);
    let x = f272(x);
    let x = f273(x);
    let x = f274(x);
    let x = f275(x);
    let x = f276(x);
    let x = f277(x);
    let x = f278(x);
    let x = f279(x);
    let x = f280(x);
    let x = f281(x);
    let x = f282(x);
    let x = f283(x);
    let x = f284(x);
    let x = f285(x);
    let x = f286(x);
    let x = f287(x);
    let x = f288(x);
    let x = f289(x);
    let x = f290(x);
    let x = f291(x);
    let x = f292(x);
    let x = f293(x);
    let x = f294(x);
    let x = f295(x);
    let x = f296(x);
    let x = f297(x);
    let x = f298(x);
    let x = f299(x);
    let x = f300(x);
    x
}

pub trait TBug {
    fn run(&self, a: u8) -> u8;
}
pub struct CBug;
impl TBug for CBug {
    fn run(&self, a: u8) -> u8 {
        big_bug(a)
    }
}
impl TBug for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

pub trait TSafe {
    fn run(&self, a: u8) -> u8;
}
pub struct CSafe;
impl TSafe for CSafe {
    fn run(&self, a: u8) -> u8 {
        big_safe(a)
    }
}
impl TSafe for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

pub trait TEarly {
    fn run(&self, a: u8) -> u8;
}
pub struct CEarly;
impl TEarly for CEarly {
    fn run(&self, a: u8) -> u8 {
        big_early_bug(a)
    }
}
impl TEarly for Other {
    fn run(&self, a: u8) -> u8 {
        a
    }
}

#[kani::proof]
fn bug_obligation_past_budget_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TBug> = if kani::any() { Box::new(CBug) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
fn safe_obligation_free_past_budget_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TSafe> = if kani::any() { Box::new(CSafe) } else { Box::new(Other) };
    sink(o.run(a));
}

#[kani::proof]
fn bug_obligation_before_budget_multi() {
    let a: u8 = kani::any();
    let o: Box<dyn TEarly> = if kani::any() { Box::new(CEarly) } else { Box::new(Other) };
    sink(o.run(a));
}
