import { print_i63, print_compare, print_bool, print_nat_sexp, print_nat_notation, print_list_sexp, print_list_notation, print_option, print_prod, print_positive_sexp, print_N_sexp, print_Z_sexp, print_compcert_byte_sexp } from './modules/pp.js';

const pp_map = {
    "demo1": (val, dataView) => print_list_sexp(val, dataView, print_bool),
    "demo2": (val, dataView) => print_list_sexp(val, dataView, print_bool),
    "list_sum": print_nat_sexp,
    "vs_easy": print_bool,
    "vs_hard": print_bool,
    "binom": print_nat_sexp,
    "color": (val, dataView) => print_prod(val, dataView, print_Z_sexp, print_Z_sexp),
    "sha_fast": (val, dataView) => print_list_sexp(val, dataView, print_compcert_byte_sexp),
    "ack_3_9": print_nat_sexp,
    "even_10000": print_bool,
    "bernstein_yang": print_Z_sexp,
    "sm_gauss_nat": (val, dataView) => print_option(val, dataView, print_nat_sexp),
    "sm_gauss_N": (val, dataView) => print_option(val, dataView, print_N_sexp),
    "sm_gauss_PrimInt": (val, dataView) => print_option(val, dataView, print_i63),
    "coqprime": print_bool,
};

import { readFileSync } from 'fs';

var args = process.argv.slice(2);
if (args.length != 2) {
    console.log("Expected two args: 0: path to folder containing wasm file to run, 1: program.");
    console.log("e.g.: $ node ./js/run_wasm_external_pp.js ./ vs_easy");
    process.exit(1);
}

let path = args[0];

if (path.charAt(path.length - 1) != "/") { path = path + "/" }

const program = args[1];

let importObject = { env: {} };

(async () => {
    const start_startup = Date.now();
    const bytes = readFileSync(path + `CertiRocq.Tests.tests.${program}.wasm`);

    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), importObject
    );
    const stop_startup = Date.now();
    const time_startup = stop_startup - start_startup;

    const prime_pattern = /^prime.*$/;
    const primitive_pattern = /.*_primitive.*$/;

    try {
	const start_main = Date.now();
        obj.instance.exports.main_function();
        const stop_main = Date.now();
        const time_main = stop_main - start_main;

        if (obj.instance.exports.out_of_mem.value == 1) {
            console.log("Ran out of memory.");
            console.log(`Benchmark ${path}: {{"time_startup": "${time_startup}", "time_main": "${time_main}", "program": "${program}"}} (in ms)`);
            process.exit(1);
        }

	let bytes = obj.instance.exports.mem_ptr.value;
        let time_pp = undefined;

	// pretty printing
	var pp_fun;
	if (prime_pattern.test(program)) { pp_fun = print_bool; }
	else if (primitive_pattern.test(program)) { pp_fun = print_bool; }
	else { pp_fun = pp_map[program]; }

	if (pp_fun) {
	    const memory = obj.instance.exports.memory;
	    const dataView = new DataView(memory.buffer);
	    const res_value = obj.instance.exports.result.value;
	    process.stdout.write(`${program} ====> `);

	    const start_pp = Date.now();
	    pp_fun(res_value, dataView);
	    const stop_pp = Date.now();
	    time_pp = stop_pp - start_pp;
	    process.stdout.write("\n");

	} else {
	    console.log(`No pretty function defined for program ${program}`);
        }

	if (!(primitive_pattern.test(program))) {
	    console.log(`Benchmark ${path}: {{"time_startup": "${time_startup}", "time_main": "${time_main}", "time_pp": "${time_pp}", "program": "${program}"}} (in ms)`);
	}
    } catch (error) {
	console.log(error);
	process.exit(1);
    }})();
