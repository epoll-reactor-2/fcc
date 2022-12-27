// 60
int sum(int *array, int size) {
    int result = 0;
    for (int i = 0; i < size; ++i) {
        result += array[i];
    }
    return result;
}

int main() {
    int array[3];
    array[0] = 10;
    array[1] = 20;
    array[2] = 30;
    return sum(array, 3);
}
