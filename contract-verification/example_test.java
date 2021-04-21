import java.util.Arrays;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

public class SortTest {
  
  @Test
  void sortArrayTest() {
    Integer[] array = {5, 13, 1};
    Arrays.sort(array);
    Assertions.assertTrue(array[0] == 1);
    Assertions.assertTrue(array[1] == 5);
    Assertions.assertTrue(array[2] == 13);
  }

}