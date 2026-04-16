#include <caml/mlvalues.h>

extern value rocq_msg_debug(value msg);
extern value rocq_msg_info(value msg);
extern value rocq_user_error(value msg);

extern value metarocq_guard_impl(value fixcofix, value globalenv, value context, value term);
