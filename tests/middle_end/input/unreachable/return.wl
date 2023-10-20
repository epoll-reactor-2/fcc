//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   t0 = t0(@noalias) + 1
//       3:   ret 0
int main() {
    int a = 1;
    ++a;
    return 0;
    --a;
    return 1;
    return 2;
}