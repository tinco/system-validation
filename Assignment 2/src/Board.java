/**
 * Represents the board of the game. The board is by default always square.
 */
final class Board {

  /*@ spec_public */ int xSize;
  /*@ spec_public */ int ySize;

  //@ public invariant xSize > 0 && ySize > 0;

  /*@ spec_public */ /*@ non_null */ BoardItem[][] items;

  /** @informal: The board contents has the right declared size
         and is completely filled with non null elements. Moreover,
         the items that are placed on the board have consistent position
         information -- their stored position is the one they occupy 
         on the board. */
  //@ public invariant items.length == xSize;
  //@ public invariant (\forall int i; 0 <= i && i < xSize; items[i].length == ySize);  

  /** @informal: Based on the valid size input creates an empty board of
         that size. */
  //@ requires xSize > 0 && ySize > 0;
  //@ ensures (\forall int x,y; 0 <= x && 0 <= y && x < xSize && y < ySize; items[x][y] instanceof Ground);
  Board (int xSize, int ySize) {
    this.xSize = xSize;
    this.ySize = ySize;
    items = new BoardItem[xSize][ySize];
    for (int x = 0; x < xSize; x++) {
      for (int y = 0; y < ySize; y++) {
        items[x][y] = new Ground (new Position (x, y));
      }
    }
  }

  /** Used to build some meaningful game board. */
  /** @informal: only items with predeclared correct position
        information are allowed to be put on the board. */
  //@ requires item.position().x >= 0 && item.position().x < xSize;
  //@ requires item.position().y >= 0 && item.position().y < ySize;
  void putItemOnBoard (BoardItem item) {
    items[item.position().x][item.position().y] = item;
  }

}
