//fun identity(int * t0):
//       0:   ret *t0
//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = call identity(&t0)
//       4:   ret t1
int identity(int *ptr) {
    return *ptr;
}

int main() {
    int a = 1;
    return identity(&a);
}