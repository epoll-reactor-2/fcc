//fun identity(int * t0):
//       0:   int * t1
//       1:   t1 = t0
//       2:   ret *t1
//fun main():
//       0:   int t0
//       1:   t0 = 1
//       2:   int t1
//       3:   t1 = t0
//       4:   int t2
//       5:   t2 = call identity(&t1)
//       6:   ret t2
int identity(int *ptr) {
    return *ptr;
}

int main() {
    int a = 1;
    return identity(&a);
}