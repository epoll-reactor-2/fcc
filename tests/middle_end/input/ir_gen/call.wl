//fun f(int t0, int t1, int t2):
//       0:   int t3
//       1:   int t4
//       2:   t4 = t1 + t2
//       3:   t3 = t0 + t4
//       4:   ret t3
//fun main():
//       0:   int t0
//       1:   t0 = call f(1, 2, 3)
//       2:   ret t0
int f(int a, int b, int c) {
    return a + b + c;
}

int main() {
    return f(1, 2, 3);
}