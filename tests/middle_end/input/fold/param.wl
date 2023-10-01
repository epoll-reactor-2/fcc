//fun f(int t0, int t1):
//       0:   int t2
//       1:   t2 = 10
//       2:   int t3
//       3:   int t4
//       4:   int t5
//       5:   int t6
//       6:   t6 = 12
//       7:   t5 = t0 * 12
//       8:   t4 = t5 + t1
//       9:   t3 = t4 << 10
//      10:   ret t3
int f(int a, int b)
{
    int const = 10;

    return a * (const + 2) + b << const;
}