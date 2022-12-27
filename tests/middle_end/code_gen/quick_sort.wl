// 1
void swap(int *lhs, int *rhs) {
    int tmp = *lhs;
    *lhs = *rhs;
    *rhs = tmp;
}

int partition(int *mem, int low, int high) {
    int pivot = mem[high];
    int i = low - 1;

    for (int j = low; j < high; ++j) {
        if (mem[j] <= pivot) {
            ++i;
            swap(&mem[i], &mem[j]);
        }
    }
    swap(&mem[i + 1], &mem[high]);
    return i + 1;
}

void quick_sort(int *mem, int low, int high) {
    if (low < high) {
        int part = partition(mem, low, high);
        quick_sort(mem, low, part - 1);
        quick_sort(mem, part + 1, high);
    }
}

int main() {
    int array[5];
    array[0] =  14;
    array[1] =   7;
    array[2] =  23;
    array[3] =   0;
    array[4] = 119;
    quick_sort(array, 0, 4);

    return
    array[0] ==   0 &&
    array[1] ==   7 &&
    array[2] ==  14 &&
    array[3] ==  23 &&
    array[4] == 119
    ;
}
