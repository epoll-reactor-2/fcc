// 1
int main() {
    int array[2];
    array[0] = 666;
    array[1] = 333;
    ++array[1];
    return (array[0] + array[1]) == 1000;
}