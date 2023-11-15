//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int * t1
//       3:   int t2
//       4:   t2 = t0
//       5:   t1 = &t2
//       6:   int * t3
//       7:   int * t4
//       8:   t4 = t1
//       9:   t3 = &t4
//      10:   int * t5
//      11:   int * t6
//      12:   t6 = t3
//      13:   t5 = &t6
//      14:   int * t7
//      15:   int * t8
//      16:   t8 = t5
//      17:   t7 = &t8
//      18:   int * t9
//      19:   t9 = t7
//      20:   int * t10
//      21:   t10 = *t9
//      22:   int * t11
//      23:   t11 = *t10
//      24:   int * t12
//      25:   t12 = *t11
//      26:   ret *t12
int main() {
    int     a = 1;
    int    *b = &a;
    int   **c = &b;
    int  ***d = &c;
    int ****e = &d;

    return ****e;
}