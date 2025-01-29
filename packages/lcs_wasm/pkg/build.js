import * as wasm from "./build_bg.wasm";
export * from "./build_bg.js";
import { __wbg_set_wasm } from "./build_bg.js";
__wbg_set_wasm(wasm);