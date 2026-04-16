import { print_i63, print_compare, print_bool, print_nat_sexp, print_nat_notation, print_list_sexp, print_list_notation, print_option, print_prod, print_positive_sexp, print_N_sexp, print_Z_sexp, print_compcert_byte_sexp, print_carry } from './modules/pp.js';

const tests = [
    ["add1", print_i63, "5"],
    ["add2", print_i63, "0"],
    ["addc1", (val, dataView) => print_carry(val, dataView, print_i63), "C0 5"],
    ["addc2", (val, dataView) => print_carry(val, dataView, print_i63), "C1 1"],
    ["addcarryc1", (val, dataView) => print_carry(val, dataView, print_i63), "C0 6"],
    ["addcarryc2", (val, dataView) => print_carry(val, dataView, print_i63), "C1 2"],
    ["sub1", print_i63, "1"],
    ["sub2", print_i63, "9223372036854775807"],
    ["subc1", (val, dataView) => print_carry(val, dataView, print_i63), "C0 1"],
    ["subc2", (val, dataView) => print_carry(val, dataView, print_i63), "C1 9223372036854775807"],
    ["subcarryc1", (val, dataView) => print_carry(val, dataView, print_i63), "C0 1"],
    ["subcarryc2", (val, dataView) => print_carry(val, dataView, print_i63), "C1 9223372036854775806"],
    ["mul1", print_i63, "6"],
    ["mul2", print_i63, "9223372036854775806"],
    ["mulc1", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 6)"],
    ["mulc2", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(1, 9223372036854775806)"],
    ["mulc3", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 0)"],
    ["mulc4", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(16, 975826582703597072)"],
    ["mulc5", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(7835138088720211561, 6616587037742705713)"],
    ["div1", print_i63, "2"],
    ["div2", print_i63, "1"],
    ["div3", print_i63, "0"],
    ["mod1", print_i63, "0"],
    ["mod2", print_i63, "2"],
    ["mod3", print_i63, "42"],
    ["land1", print_i63, "0"],
    ["land2", print_i63, "0"],
    ["land3", print_i63, "0"],
    ["land4", print_i63, "9223372036854775807"],
    ["lor1",print_i63, "0"],
    ["lor2",print_i63, "9223372036854775807"],
    ["lor3", print_i63, "9223372036854775807"],
    ["lor4", print_i63, "9223372036854775807"],
    ["lxor1", print_i63, "0"],
    ["lxor2", print_i63, "9223372036854775807"],
    ["lxor3", print_i63, "9223372036854775807"],
    ["lxor4", print_i63, "0"],
    ["lsl1", print_i63, "6917529027641081856"],
    ["lsl2", print_i63, "0"],
    ["lsl3", print_i63, "0"],
    ["lsr1", print_i63, "3"],
    ["lsr2", print_i63, "0"],
    ["lsr3", print_i63, "0"],
    ["compare1", print_compare, "Eq"],
    ["compare2", print_compare, "Lt"],
    ["compare3", print_compare, "Gt"],
    ["eqb1", print_bool, "true"],
    ["eqb2", print_bool, "false"],
    ["ltb1", print_bool, "false"],
    ["ltb2", print_bool, "true"],
    ["ltb3", print_bool, "false"],
    ["leb1", print_bool, "true"],
    ["leb2", print_bool, "true"],
    ["leb3", print_bool, "false"],
    ["head0_1", print_i63, "61"],
    ["head0_2", print_i63, "0"],
    ["head0_3", print_i63, "63"],
    ["tail0_1", print_i63, "61"],
    ["tail0_2", print_i63, "0"],
    ["tail0_3", print_i63, "63"],
    ["diveucl1", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(2, 0)"],
    ["diveucl2", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(1, 2)"],
    ["diveucl3", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 42)"],    
    ["diveucl_21_1", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(4611686018427387904, 1)"],
    ["diveucl_21_2", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 0)"],
    ["diveucl_21_3", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 0)"],
    ["diveucl_21_4", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(0, 0)"],
    ["diveucl_21_5", (val, dataView) => print_prod(val, dataView, print_i63, print_i63), "(17407905077428, 3068214991893055266)"],
    ["addmuldiv1", print_i63, "12887523328"],
    ["addmuldiv2", print_i63, "0"],
    ["addmuldiv3", print_i63, "9223372036854775807"],
    ["unsigned1", print_i63, "0"],
    ["unsigned2", print_i63, "3"],
];

import { readFileSync } from 'fs';

let importObject = { env: {} };

async function run_test([test, pp_fun, expected]) {
    const bytes = readFileSync(`CertiRocq.Tests.uint63_unit_tests.${test}.wasm`);

    const obj = await WebAssembly.instantiate(
        new Uint8Array (bytes), importObject
    );

    obj.instance.exports.main_function();
    const memory = obj.instance.exports.memory;
    const dataView = new DataView(memory.buffer);
    const res_value = obj.instance.exports.result.value;

    const stdout = process.stdout.write.bind(process.stdout);

    let result = "";

    process.stdout.write = (chunk, encoding, callback) => {
	if (typeof chunk === 'string') {
	    result += chunk;
	}
    };

    pp_fun(res_value, dataView);

    process.stdout.write = stdout;

    return new Promise((resolve, reject) => {
	if (!(result === expected)) {
	    reject(`${test}: expected ${expected}, got ${result}`);
	} else {
	    resolve();
	}
    });

};

Promise.allSettled(tests.map(run_test))
    .then((results) => {
	const errors = results.filter((r) => r.status === "rejected");
	if (errors.length ==0) {
	    console.log("All tests passed!");
	} else {
	    console.log("Some tests failed:");
	    errors.forEach((e) => console.log(e.reason));
	}}).catch();
