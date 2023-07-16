//fun f(alloca int %0, alloca int %1, alloca int %2):
//       0:   alloca int %3
//       1:   alloca int %4
//       2:   store %4 %1 add %2
//       3:   store %3 %0 add %4
//       4:   ret %3
//fun main():
//       0:   alloca int %0
//       1:   store %0 call f($1, $2, $3)
//       2:   ret %0
int f(int a, int b, int c) {
    return a + b + c;
}

int main() {
    return f(1, 2, 3);
}