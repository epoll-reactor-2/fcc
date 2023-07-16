//fun f(alloca int %0, alloca int %1):
//       0:   alloca int %2
//       1:   store %2 $10
//       2:   alloca int %3
//       3:   alloca int %4
//       4:   alloca int %5
//       5:   alloca int %6
//       6:   store %6 $12
//       7:   store %5 %0 mul $12
//       8:   store %4 %5 add %1
//       9:   store %3 %4 shl $10
//      10:   ret %3
int f(int a, int b)
{
    int const = 10;

    return a * (const + 2) + b << const;
}