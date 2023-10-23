//fun f_1():
//       0:   int t0
//       1:   int t1
//       3:   int t3
//       8:   int t4(@loop)
//      10:   int t5
//      15:   int t6(@loop)
//       2:   int t2
//       4:   t3 = 10 + 1
//       5:   t2 = 100 + t3
//       6:   t1 = 1000 + t2
//       7:   t0 = t1
//       9:   t4 = 0(@loop)
//      11:   | t5 = t4 < t0
//      12:   | if t5 != 0 goto L14
//      13:   | jmp L18
//      14:   | t0 = t0(@noalias) - 1
//      16:   | t6 = t4 <<= 1(@loop)
//      17:   | jmp L12
//      18:   ret
//fun f_2():
//       0:   int t0
//       1:   int t1
//       3:   int t3
//       4:   int t4
//       2:   int t2
//       5:   t4 = call f_2()
//       6:   t3 = 4 + t4
//       7:   t2 = 3 + t3
//       8:   t1 = 2 + t2
//       9:   t0 = 1 + t1
//      10:   ret t0
//fun main():
//       0:   ret 0
void f_1() {
    int initial = 1000 + 100 + 10 + 1;
    for (int i = 0; i < initial; i <<= 1) {
        --initial;
    }
}

int f_2() {
   return 1 + 2 + 3 + 4 + f_2(); 
}

int main() {
    return 0;
}