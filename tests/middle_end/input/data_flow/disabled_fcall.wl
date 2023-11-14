//fun f():
//       0:   ret 0
//fun main():
//       0:   int t0
//       1:   t0 = 0
//       4:   t0 = t0(@noalias) + 1
//       5:   call f()
//       6:   t0 = t0(@noalias) - 1
//       8:   int t2
//       9:   t2 = call f()
//      10:   t0 = t2
//      26:   ret t0
int f() { return 0; }

int main() {
    int i = 0;
    int j = 0;
    ++i;
    f();
    --i;
    --j;
    i = f();
    j = f() + f() + f() + f();
    return i;
}