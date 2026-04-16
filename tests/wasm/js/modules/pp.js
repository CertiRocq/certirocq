const name = 'pp'

export const print_list_sexp = (val, dataView, print_elem) => {

    if (val & 1) {
	switch (val >> 1) {
	case 0:
	    process.stdout.write("nil");
	    break;
	}
    }
    else {
	const tag = dataView.getInt32(val, true);
	switch (tag) {
	case 0:
	    process.stdout.write("(cons ");

	    const head = dataView.getInt32(val+4, true);

	    print_elem(head, dataView);

	    process.stdout.write(" ");

	    const tail = dataView.getInt32(val+8, true);

	    print_list_sexp(tail, dataView, print_elem);

	    process.stdout.write(")");

	    break;
	}
    }
}

const print_list_notation_aux = (val, dataView, print_elem) => {
    if (val & 1) {
	return;
    } else {

	const head = dataView.getInt32(val + 4, true);
	print_elem(head, dataView);
	const tail = dataView.getInt32(val + 8, true);
	if (!(tail & 1)) { process.stdout.write(" ; "); }
	print_list_notation_aux(tail, dataView, print_elem);
    }
}

export const print_list_notation = (val, dataView, print_elem) => {
    process.stdout.write("[ ");
    print_list_notation_aux(val, dataView, print_elem);
    process.stdout.write(" ]");
}


export const print_i63 = (ptr, dataView) => {

    const val = dataView.getBigUint64(ptr, true);

    process.stdout.write(val.toString());
}

export const print_nat_sexp = (val, dataView) => {
    if (val & 1) {
	switch (val >> 1) {
	case 0:
	    process.stdout.write("O");
	    break;
	}
    }
    else {
	const tag = dataView.getInt32(val, true);
	switch (tag) {
	case 0:
	    process.stdout.write("(S ");
	    const arg = dataView.getInt32(val + 4, true);
	    print_nat_sexp(arg, dataView);
	    process.stdout.write(")");
	    break;
	}
    }
}

const nat_to_int_rep = (val, dataView, acc) => {
    if (val & 1) {
	switch (val >> 1) {
	case 0:
	    return acc;
	}
    }
    else {
	const tag = dataView.getInt32(val, true);
	switch (tag) {
	case 0:
	    const arg = dataView.getInt32(val + 4, true);
	    return nat_to_int_rep(arg, dataView, acc + 1);
	}
    }
}

export const print_nat_notation = (val, dataView) => {
    process.stdout.write(nat_to_int_rep(val, dataView, 0).toString());
}


// the constructors of bools are swapped, see https://github.com/CertiRocq/certirocq/pull/100
export const print_bool = (val, dataView) => {
    if (val & 1) {
	switch (val >> 1) {
	case 1:
	    process.stdout.write("true");
	    break;
	case 0:
	    process.stdout.write("false");
	    break;
	}
    }
    else {}
}

export const print_compare = (val, dataView) => {
    if (val & 1) {
	switch (val >> 1) {
	case 0:
	    process.stdout.write("Eq");
	    break;
	case 1:
	    process.stdout.write("Lt");
	    break;
	case 2:
	    process.stdout.write("Gt");
	    break;
	}
    }
    else {}
}

export const print_option = (val, dataView, print_elem) => {
    if (val & 1) {
	process.stdout.write("None");
    }
    else {
	process.stdout.write("Some ");
	const arg = dataView.getInt32(val + 4, true);
	print_elem(arg, dataView);
    }
}

export const print_prod = (val, dataView, print_elem1, print_elem2) => {
    process.stdout.write("(");
    const arg1 = dataView.getInt32(val + 4, true);
    print_elem1(arg1, dataView);
    process.stdout.write(", ");
    const arg2 = dataView.getInt32(val + 8, true);
    print_elem2(arg2, dataView);
    process.stdout.write(")");
}

export const print_positive_sexp = (val, dataView) => {
    if (val & 1) {
	process.stdout.write("xH");
    }
    else {
	const tag = dataView.getInt32(val, true);
	switch (tag) {
	case 0:
	    process.stdout.write("(xI ");
	    break;
	case 1:
	    process.stdout.write("(xO ");
	    break;
	}
	let arg = dataView.getInt32(val + 4, true);
	print_positive_sexp(arg, dataView);
	process.stdout.write(")");

    }
}

export const print_N_sexp = (val, dataView) => {
    if (val & 1) {
	process.stdout.write("N0");
    }
    else {
	process.stdout.write("(Npos ");
	const arg = dataView.getInt32(val + 4, true);
	print_positive_sexp(arg, dataView);
	process.stdout.write(")");
    }
}

export const print_Z_sexp = (val, dataView) => {
    if (val & 1) {
	process.stdout.write("Z0");
    }
    else {
	const tag = dataView.getInt32(val, true);
	switch (tag) {
	case 0:
	    process.stdout.write("(Zpos ");
	    break;
	case 1:
	    process.stdout.write("(Zneg ");
	    break;
	}
	const arg = dataView.getInt32(val + 4, true);
	print_positive_sexp(arg, dataView);
	process.stdout.write(")");
    }
}

export const print_compcert_byte_sexp = (val, dataView) => {
    process.stdout.write("(mkint ");
    const arg = dataView.getInt32(val + 4, true);
    print_Z_sexp(arg, dataView);
    process.stdout.write(")");
}

export const print_carry = (val, dataView, print_elem) => {
    const tag = dataView.getInt32(val, true);
    switch (tag) {
    case 0:
	process.stdout.write("C0 ");
	break;
    case 1:
	process.stdout.write("C1 ");
	break;
    }
	const arg = dataView.getInt32(val + 4, true);
	print_elem(arg, dataView);
}
