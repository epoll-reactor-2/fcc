//2
int main() {
    int a = 3;
    int *ptr = &a;
    a = 2;
    return *ptr;
}