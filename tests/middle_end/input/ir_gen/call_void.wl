//fun f(alloca int %0, alloca int %1, alloca int %2):
//       0:   alloca int %3
//       1:   alloca int %4
//       2:   alloca int %5
//       3:   store %5 %1 add %2
//       4:   store %4 %0 add %5
//       5:   store %3 %4
//       6:   ret
//fun main():
//       0:   call f($1, $2, $3)
//       1:   ret $0
void f(int a, int b, int c) {
    int r = a + b + c;
}

int main() {
    f(1, 2, 3);
    return 0;
}