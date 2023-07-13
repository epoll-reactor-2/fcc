//fun main():
//       0:   alloca int %0
//       1:   store %0 $1
//       2:   alloca int %1
//       3:   store %1 $1
//       4:   alloca int %2
//       5:   store %2 $1
//       6:   alloca int %3
//       7:   store %3 $1
//       8:   store %1 $2
//       9:   store %3 $2
//      10:   store %2 %0
//      11:   alloca int %4
//      12:   store %4 %1 add %3
//      13:   ret %4
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