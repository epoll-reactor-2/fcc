//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = 1
//       4:   int t2
//       5:   t2 = 1
//       6:   int t3
//       7:   t3 = 1
//       8:   t1 = 2
//       9:   t3 = 2
//      10:   t2 = t0
//      11:   int t4
//      12:   t4 = t1 + t3
//      13:   ret t4
int main() {
    int a = 1;
    int b = 1;
    int c = 1;
    int d = 1;
    b = 2;
    d = 2;
    c = a;
    return b + d;
}