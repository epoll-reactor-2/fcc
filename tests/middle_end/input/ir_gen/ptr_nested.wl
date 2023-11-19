//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int * t1
//       3:   t1 = &t0
//       4:   int * t2
//       5:   t2 = &t1
//       6:   int * t3
//       7:   t3 = &t2
//       8:   int * t4
//       9:   t4 = &t3
//      10:   int * t5
//      11:   t5 = *t4
//      12:   int * t6
//      13:   t6 = *t5
//      14:   int * t7
//      15:   t7 = *t6
//      16:   ret *t7
int main() {
    int     a = 1;
    int    *b = &a;
    int   **c = &b;
    int  ***d = &c;
    int ****e = &d;

    return ****e;
}