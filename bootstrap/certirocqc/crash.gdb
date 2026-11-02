set follow-fork-mode child
handle SIGSEGV stop
run
bt 12
python
import gdb
def run(cmd):
    try:
        return gdb.execute(cmd, to_string=True).strip()
    except gdb.error as e:
        return "error: %s" % e
f = gdb.newest_frame()
while f is not None:
    if f.name() == "f_case_known_9904":
        try:
            l = int(f.read_var("$l_94258"))
            print("kn2 = 0x%x: %s" % (l, run("info symbol 0x%x" % l)))
            print(run("x/4gx 0x%x" % (l - 8)))
        except Exception as e:
            print("cannot read kn2: %s" % e)
    f = f.older()
end
info proc mappings
