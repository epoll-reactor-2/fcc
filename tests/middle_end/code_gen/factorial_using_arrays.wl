// 120
int main() {
    int array[5];

    for (int i = 1; i < 6; ++i) {
    	array[i - 1] = i;
    }

    int sum = 1;

    for (int i = 0; i < 5; ++i) {
    	sum *= array[i];
    }

    return sum;
}