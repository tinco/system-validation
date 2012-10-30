/**
 * The game of Sokoban is played on a (for simplicity) square board. Each
 * cell of the board is occupied by either:
 *   
 *   - a wall, which is impenetrable
 *   - a ground that can be marked. Marked ground squares have to be covered with
 *     crates to win the game
 *   - a box/crate that can be moved one cell in a horizontal or vertical direction,
 *     provided there is no obstruction behind the crate
 *   - a player itself, that is initially placed on an unoccupied spot and
 *     can move horizontally or vertically keeping in mind the game rules.
 * 
 * The game is won when the player rearranges the board such that all marked ground
 * squares are covered by crates.
 */
final class Game {
  /*@ public model boolean gameWon;
    @ private represents gameWon <-
    @     (\forall int x; 0 <= x && x < board.xSize;
    @         (\forall int y; 0 <= y && y < board.ySize;
    @             (board.items[x][y].isMarked () && (board.items[x][y] instanceof Crate)) ||
    @              !board.items[x][y].isMarked ()
    @               ));
  */

  /*@ spec_public */ /*@ non_null */ Board board;
  /*@ spec_public */ Player player;

  /** @informal: Some consistency properties:
    *   - A player has to be within the bounds of the board
    *   - A player can only stand on an "can stand on" board square 
    */
  //@ public invariant player.position().x >= 0 && player.position().x < board.xSize;
  //@ public invariant player.position().y >= 0 && player.position().y < board.ySize;
  //@ public invariant board.items[player.position().x][player.position().y].isCanStepOn();

  /** @informal: Based on a board and a validly referenced player with respect to this
         board (see above) create new game with this board and player. */
  //@ ensures this.board == board && this.player == player;
  Game (Board board, Player player) {
    this.board = board;
    this.player = player;
  }

  /** @informal: Check for the win situation. Successful result implies
          all marked positions have to have boxes on top. */
  //@ ensures \result == gameWon;
  boolean wonGame () {
    boolean result = true;

    //@ loop_invariant x >= 0;
    for (int x = 0; x < board.xSize; x++) {
      if (!checkWonRow (board.items[x])) {
        result = false;
        break;
      }
    }
    return result;
  }

  /** Helper method for the above, ESC/Java2 does not deal well (this is 
    * an understatement) with nested loops.
    */
  //@ requires row.length == board.ySize;
  //@ requires (\forall int y; 0 <= y && y < board.ySize; row[y] != null);
  private boolean checkWonRow (BoardItem[] row) {
    boolean result = true;

    //@ loop_invariant y >= 0;
    for (int y = 0; y < board.ySize; y++) {
      if (row[y].isMarked () && !(row[y] instanceof Crate)) {
        result = false;
        break;
      }
    }
    return result;
  }

  /** The core of the game. Checks the validity of the move,
    *  moves the player to new position, rearranges the board
    *  accordingly.
    */
  /** @informal: a successful move means that the position of the player
         was changed to the requested one. The method requires a
         valid next position. */
  //@ requires player.position().isValidNextPosition(newPosition);
  boolean movePlayer (Position newPosition) {

    // @informal: Pre check that the new position is on the board.
    //@ assert newPosition.x >= 0 && newPosition.x < board.xSize;
    //@ assert newPosition.y >= 0 && newPosition.y < board.ySize;

    // If the new position is ground just move
    if (board.items[newPosition.x][newPosition.y].isCanStepOn ()) {
      player.setPosition (newPosition);
      return true;
    }
    // Then, if the new position is occupied by something solid, skip
    if (!board.items[newPosition.x][newPosition.y].isMovable ()) {
      return false;
    }

    // Last case, it has to be something movable,
    // make the move together with the item if possible.
    //
    // @informal: make sure with a check that the target
    //   item on the board is indeed movable.
    //@ assert board.items[newPosition.x][newPosition.y].isMovable();

    int xShift = newPosition.x - player.position ().x;
    int yShift = newPosition.y - player.position ().y;
    // The new position of the moved item:
    int nX = newPosition.x + xShift;
    int nY = newPosition.y + yShift;
    // See if we end up outside of the board and that the crate can be moved
    if (!(nX >= 0 && nX < board.xSize && nY >= 0 && nY < board.ySize)
	|| !board.items[nX][nY].isCanStepOn ()) {
      return false;
    }
    // Move the crate, change markings accordingly.
    Position newCratePosition = new Position (nX, nY);
    boolean wasMarked = board.items[newPosition.x][newPosition.y].isMarked ();
    boolean newMarked =
      board.items[newCratePosition.x][newCratePosition.y].isMarked ();

    board.items[newCratePosition.x][newCratePosition.y] = newMarked ?
      new MarkedCrate (newCratePosition) : new Crate (newCratePosition);
    board.items[newPosition.x][newPosition.y] = wasMarked ?
      new MarkedGround (newPosition) : new Ground (newPosition);

    player.setPosition (newPosition);
    return true;
  }

  public String toString (){
    String r = "Game[ ";
    for (int x = 0; x < board.xSize; x++) {
      for (int y = 0; y < board.ySize; y++) {
        r += board.items[x][y] + ", ";
      }
    }
    r += player.toString () + " ]";
    return r;
  }

  public static void main (String[]args) {
    Board b = new Board (9, 9);
    b.putItemOnBoard (new Wall (new Position (0, 0)));
    b.putItemOnBoard (new Wall (new Position (0, 1)));
    b.putItemOnBoard (new Wall (new Position (0, 2)));
    b.putItemOnBoard (new Wall (new Position (0, 3)));
    b.putItemOnBoard (new Wall (new Position (0, 4)));
    b.putItemOnBoard (new Wall (new Position (0, 5)));
    b.putItemOnBoard (new Wall (new Position (0, 6)));
    b.putItemOnBoard (new Wall (new Position (0, 7)));
    b.putItemOnBoard (new Wall (new Position (0, 8)));
    b.putItemOnBoard (new Wall (new Position (8, 0)));
    b.putItemOnBoard (new Wall (new Position (8, 1)));
    b.putItemOnBoard (new Wall (new Position (8, 2)));
    b.putItemOnBoard (new Wall (new Position (8, 3)));
    b.putItemOnBoard (new Wall (new Position (8, 4)));
    b.putItemOnBoard (new Wall (new Position (8, 5)));
    b.putItemOnBoard (new Wall (new Position (8, 6)));
    b.putItemOnBoard (new Wall (new Position (8, 7)));
    b.putItemOnBoard (new Wall (new Position (8, 8)));
    b.putItemOnBoard (new Wall (new Position (1, 0)));
    b.putItemOnBoard (new Wall (new Position (2, 0)));
    b.putItemOnBoard (new Wall (new Position (3, 0)));
    b.putItemOnBoard (new Wall (new Position (4, 0)));
    b.putItemOnBoard (new Wall (new Position (5, 0)));
    b.putItemOnBoard (new Wall (new Position (6, 0)));
    b.putItemOnBoard (new Wall (new Position (7, 0)));
    b.putItemOnBoard (new Wall (new Position (1, 8)));
    b.putItemOnBoard (new Wall (new Position (2, 8)));
    b.putItemOnBoard (new Wall (new Position (3, 8)));
    b.putItemOnBoard (new Wall (new Position (4, 8)));
    b.putItemOnBoard (new Wall (new Position (5, 8)));
    b.putItemOnBoard (new Wall (new Position (6, 8)));
    b.putItemOnBoard (new Wall (new Position (7, 8)));
    b.putItemOnBoard (new Crate (new Position (1, 1)));
    b.putItemOnBoard (new Crate (new Position (1, 3)));
    b.putItemOnBoard (new Crate (new Position (1, 5)));
    b.putItemOnBoard (new Crate (new Position (1, 7)));
    b.putItemOnBoard (new Crate (new Position (7, 1)));
    b.putItemOnBoard (new Crate (new Position (7, 3)));
    b.putItemOnBoard (new Crate (new Position (7, 5)));
    b.putItemOnBoard (new Crate (new Position (7, 7)));
    b.putItemOnBoard (new Crate (new Position (3, 1)));
    b.putItemOnBoard (new Crate (new Position (5, 1)));
    b.putItemOnBoard (new Crate (new Position (7, 1)));
    b.putItemOnBoard (new Crate (new Position (3, 7)));
    b.putItemOnBoard (new Crate (new Position (5, 7)));
    b.putItemOnBoard (new Crate (new Position (2, 2)));
    b.putItemOnBoard (new Crate (new Position (2, 4)));
    b.putItemOnBoard (new Crate (new Position (2, 6)));
    b.putItemOnBoard (new Crate (new Position (6, 2)));
    b.putItemOnBoard (new Crate (new Position (6, 4)));
    b.putItemOnBoard (new Crate (new Position (6, 6)));
    b.putItemOnBoard (new MarkedGround (new Position (1, 2)));
    b.putItemOnBoard (new MarkedGround (new Position (1, 4)));
    b.putItemOnBoard (new MarkedGround (new Position (1, 6)));
    b.putItemOnBoard (new MarkedGround (new Position (7, 2)));
    b.putItemOnBoard (new MarkedGround (new Position (7, 4)));
    b.putItemOnBoard (new MarkedGround (new Position (7, 6)));
    Player p = new Player (new Position (4, 4));
    Game g = new Game (b, p);
    new GameGUI (g);		// NOTE comment this out for JMLUnitNG part of the homework
  }
}
