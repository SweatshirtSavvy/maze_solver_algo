`timescale 1ns/1ps

/*
# Theme:            MazeSolver Bot
# File Description: DFS-based maze exploration. 
# Optimizations:    X/Y grid tracking, memory-inferred pathing, 
#                   and ghost-data elimination.
*/

module t2c_maze_explorer (
    input  wire clk,
    input  wire rst_n,
    input  wire left,
    input  wire mid,
    input  wire right,
    output reg  [2:0] move
);

    // ========================================
    // PARAMETERS & CONSTANTS
    // ========================================
    localparam SPAWN_POS = 8'h84; // Y=8, X=4
    localparam EXIT_POS  = 8'h04; // Y=0, X=4
    
    localparam MOVE_IDLE    = 3'b000;
    localparam MOVE_FORWARD = 3'b001;
    localparam MOVE_LEFT    = 3'b010;
    localparam MOVE_RIGHT   = 3'b011;
    localparam MOVE_UTURN   = 3'b100;
    
    localparam DIR_NORTH = 2'b00;
    localparam DIR_EAST  = 2'b01;
    localparam DIR_SOUTH = 2'b10;
    localparam DIR_WEST  = 2'b11;
    
    localparam STATE_WAIT      = 2'b00;
    localparam STATE_SENSE     = 2'b01;
    localparam STATE_EXECUTE   = 2'b10;
    localparam STATE_SAVE_PATH = 2'b11; 
    
    localparam PHASE_EXPLORE    = 2'b00;
    localparam PHASE_GO_TO_EXIT = 2'b10;
    
    parameter STACK_DEPTH = 64;
    
    // ========================================
    // REGISTERS
    // ========================================
    reg [1:0] state, next_state;
    reg [1:0] wait_counter;
    reg [1:0] phase;
    
    reg [3:0] curr_x, curr_y;
    reg [1:0] current_dir;
    
    reg [255:0] visited_map; 
    reg [5:0] stack_ptr;
    reg [5:0] copy_ptr;
    
    reg exit_found;
    reg [5:0] exit_path_length;
    reg [5:0] exit_path_index;
    
    reg backtrack_mode;
    reg dead_end_flag;
    reg do_backtrack;
    reg [1:0] chosen_direction;
    reg push_to_stack;
    reg [9:0] stack_data_in;

    // ========================================
    // MEMORY ARRAYS (RAM INFERENCE)
    // ========================================
    // Removed exit_path_positions entirely. Massive logic save.
    reg [9:0] stack_data [0:STACK_DEPTH-1]; 
    reg [1:0] exit_path_directions [0:STACK_DEPTH-1];
    
    // ========================================
    // HELPER FUNCTIONS
    // ========================================
    function [1:0] left_dir(input [1:0] dir); left_dir = dir - 2'd1; endfunction
    function [1:0] right_dir(input [1:0] dir); right_dir = dir + 2'd1; endfunction
    function [1:0] reverse_dir(input [1:0] dir); reverse_dir = dir + 2'd2; endfunction
    
    function [2:0] calc_turn(input [1:0] from_dir, input [1:0] to_dir);
        reg [1:0] diff;
        begin
            diff = to_dir - from_dir;
            case (diff)
                2'b00: calc_turn = MOVE_FORWARD;
                2'b01: calc_turn = MOVE_RIGHT;
                2'b11: calc_turn = MOVE_LEFT;
                2'b10: calc_turn = MOVE_UTURN;
            endcase
        end
    endfunction

    // ========================================
    // COMBINATIONAL PATH CALCULATIONS
    // ========================================
    wire [7:0] current_pos = {curr_y, curr_x};
    
    // Unsigned offset math - overflow naturally rolls to 15 (which fails the <9 check)
    wire [3:0] n_x = curr_x;         wire [3:0] n_y = curr_y - 4'd1;
    wire [3:0] s_x = curr_x;         wire [3:0] s_y = curr_y + 4'd1;
    wire [3:0] e_x = curr_x + 4'd1;  wire [3:0] e_y = curr_y;
    wire [3:0] w_x = curr_x - 4'd1;  wire [3:0] w_y = curr_y;

    reg [3:0] straight_x, straight_y, left_x, left_y, right_x, right_y;
    always @(*) begin
        // Straight
        case(current_dir)
            DIR_NORTH: begin straight_x = n_x; straight_y = n_y; end
            DIR_EAST:  begin straight_x = e_x; straight_y = e_y; end
            DIR_SOUTH: begin straight_x = s_x; straight_y = s_y; end
            default:   begin straight_x = w_x; straight_y = w_y; end
        endcase
        // Left
        case(left_dir(current_dir))
            DIR_NORTH: begin left_x = n_x; left_y = n_y; end
            DIR_EAST:  begin left_x = e_x; left_y = e_y; end
            DIR_SOUTH: begin left_x = s_x; left_y = s_y; end
            default:   begin left_x = w_x; left_y = w_y; end
        endcase
        // Right
        case(right_dir(current_dir))
            DIR_NORTH: begin right_x = n_x; right_y = n_y; end
            DIR_EAST:  begin right_x = e_x; right_y = e_y; end
            DIR_SOUTH: begin right_x = s_x; right_y = s_y; end
            default:   begin right_x = w_x; right_y = w_y; end
        endcase
    end

    wire [7:0] pos_straight = {straight_y, straight_x};
    wire [7:0] pos_left     = {left_y, left_x};
    wire [7:0] pos_right    = {right_y, right_x};

    // Flattened Boundary Checks: If it rolled over (e.g. 0-1 = 15) or > 8, it's false.
    wire straight_valid = (straight_x < 4'd9) && (straight_y < 4'd9);
    wire left_valid     = (left_x < 4'd9)     && (left_y < 4'd9);
    wire right_valid    = (right_x < 4'd9)    && (right_y < 4'd9);

    wire left_available = !left && left_valid && !visited_map[pos_left];
    wire straight_available = !mid && straight_valid && !visited_map[pos_straight];
    wire right_available = !right && right_valid && !visited_map[pos_right];
    wire any_unvisited = left_available || straight_available || right_available;
    
    wire at_exit = (current_pos == EXIT_POS) && (current_dir == DIR_NORTH) && !mid;
    wire stack_empty = (stack_ptr == 6'd0);
    
    wire [1:0] came_from_dir_peek = stack_data[stack_ptr - 6'd1][9:8];
    wire [7:0] source_pos_peek    = stack_data[stack_ptr - 6'd1][7:0];
    wire [1:0] target_dir_peek    = exit_path_directions[exit_path_index];
    
    // ========================================
    // STATE MACHINE TRANSITIONS
    // ========================================
    always @(*) begin
        case (state)
            STATE_WAIT:      next_state = (wait_counter == 2'd2) ? STATE_SENSE : STATE_WAIT;
            STATE_SENSE:     next_state = (phase == PHASE_EXPLORE && at_exit && !exit_found) ? 
                                          STATE_SAVE_PATH : STATE_EXECUTE;
            STATE_SAVE_PATH: next_state = (copy_ptr == stack_ptr) ? STATE_SENSE : STATE_SAVE_PATH;
            STATE_EXECUTE:   next_state = STATE_SENSE;
            default:         next_state = STATE_WAIT;
        endcase
    end
    
    // ========================================
    // SEQUENTIAL LOGIC
    // ========================================
    always @(posedge clk) begin
        if (!rst_n) begin
            state <= STATE_WAIT;
            wait_counter <= 2'd0;
            phase <= PHASE_EXPLORE;
            
            curr_y <= SPAWN_POS[7:4];
            curr_x <= SPAWN_POS[3:0];
            current_dir <= DIR_NORTH;
            
            backtrack_mode <= 1'b0;
            dead_end_flag <= 1'b0;
            do_backtrack <= 1'b0;
            
            stack_ptr <= 6'd0;
            copy_ptr <= 6'd0;
            push_to_stack <= 1'b0;
            chosen_direction <= 2'b00;
            stack_data_in <= 10'd0;
            
            exit_found <= 1'b0;
            exit_path_length <= 6'd0;
            exit_path_index <= 6'd0;
            move <= MOVE_IDLE;
            visited_map <= 256'b0;
            
        end else begin
            state <= next_state;
            
            if (state == STATE_WAIT) begin
                wait_counter <= wait_counter + 2'd1;
                move <= MOVE_IDLE;
            end
            
            else if (state == STATE_SAVE_PATH) begin
                // Dramatically simpler copy: only tracking the direction
                if (copy_ptr < stack_ptr) begin
                    exit_path_directions[copy_ptr] <= stack_data[copy_ptr][9:8];
                    copy_ptr <= copy_ptr + 6'd1;
                end
            end
            
            else if (state == STATE_SENSE) begin
                visited_map[current_pos] <= 1'b1;
                move <= MOVE_IDLE;
                
                if (phase == PHASE_EXPLORE) begin
                    if (at_exit && !exit_found) begin
                        exit_found <= 1'b1;
                        exit_path_length <= stack_ptr;
                        copy_ptr <= 6'd0; 
                    end
                    else if ((left+mid+right) == 2'd3) begin
                        dead_end_flag <= 1'b1; push_to_stack <= 1'b0;
                        do_backtrack <= 1'b0; move <= MOVE_UTURN;
                    end
                    else if (backtrack_mode) begin
                        if (any_unvisited) begin
                            backtrack_mode <= 1'b0; do_backtrack <= 1'b0;
                            if (left_available) begin
                                chosen_direction <= 2'b10; push_to_stack <= 1'b1;
                                stack_data_in <= {left_dir(current_dir), current_pos};
                                move <= MOVE_LEFT;
                            end else if (straight_available) begin
                                chosen_direction <= 2'b01; push_to_stack <= 1'b1;
                                stack_data_in <= {current_dir, current_pos};
                                move <= MOVE_FORWARD;
                            end else if (right_available) begin
                                chosen_direction <= 2'b11; push_to_stack <= 1'b1;
                                stack_data_in <= {right_dir(current_dir), current_pos};
                                move <= MOVE_RIGHT;
                            end
                        end
                        else if (!stack_empty) begin
                            do_backtrack <= 1'b1; push_to_stack <= 1'b0;
                            move <= calc_turn(current_dir, reverse_dir(came_from_dir_peek));
                        end else begin
                            backtrack_mode <= 1'b0; do_backtrack <= 1'b0; move <= MOVE_IDLE;
                            if (current_pos == SPAWN_POS) begin
                                phase <= PHASE_GO_TO_EXIT;
                                exit_path_index <= 6'd0;
                            end
                        end
                    end
                    else begin
                        do_backtrack <= 1'b0;
                        if (left_available) begin
                            chosen_direction <= 2'b10; push_to_stack <= 1'b1;
                            stack_data_in <= {left_dir(current_dir), current_pos}; move <= MOVE_LEFT;
                        end else if (straight_available) begin
                            chosen_direction <= 2'b01; push_to_stack <= 1'b1;
                            stack_data_in <= {current_dir, current_pos}; move <= MOVE_FORWARD;
                        end else if (right_available) begin
                            chosen_direction <= 2'b11; push_to_stack <= 1'b1;
                            stack_data_in <= {right_dir(current_dir), current_pos}; move <= MOVE_RIGHT;
                        end else begin
                            dead_end_flag <= 1'b1; push_to_stack <= 1'b0; move <= MOVE_UTURN;
                        end
                    end
                end
                else if (phase == PHASE_GO_TO_EXIT) begin
                    if (at_exit) begin
                        chosen_direction <= 2'b01; push_to_stack <= 1'b0;
                        do_backtrack <= 1'b0; move <= MOVE_FORWARD;
                    end
                    else if (exit_path_index < exit_path_length) begin
                        move <= calc_turn(current_dir, target_dir_peek);
                        push_to_stack <= 1'b0; do_backtrack <= 1'b0;
                    end else begin
                        move <= MOVE_IDLE;
                    end
                end
            end
            
            else if (state == STATE_EXECUTE) begin
                if (phase == PHASE_EXPLORE) begin
                    if (dead_end_flag) begin
                        current_dir <= reverse_dir(current_dir);
                        case(reverse_dir(current_dir))
                            DIR_NORTH: begin curr_x <= n_x; curr_y <= n_y; end
                            DIR_EAST:  begin curr_x <= e_x; curr_y <= e_y; end
                            DIR_SOUTH: begin curr_x <= s_x; curr_y <= s_y; end
                            default:   begin curr_x <= w_x; curr_y <= w_y; end
                        endcase
                        if (stack_ptr > 6'd0) stack_ptr <= stack_ptr - 6'd1;
                        backtrack_mode <= 1'b1; dead_end_flag <= 1'b0;
                    end
                    else if (do_backtrack) begin
                        current_dir <= reverse_dir(came_from_dir_peek);
                        curr_y <= source_pos_peek[7:4];
                        curr_x <= source_pos_peek[3:0];
                        stack_ptr <= stack_ptr - 6'd1;
                        do_backtrack <= 1'b0;
                    end
                    else if (push_to_stack && stack_ptr < (STACK_DEPTH - 6'd1)) begin
                        stack_data[stack_ptr] <= stack_data_in;
                        stack_ptr <= stack_ptr + 6'd1;
                        push_to_stack <= 1'b0;
                        
                        case (chosen_direction)
                            2'b10: begin current_dir <= left_dir(current_dir); curr_x <= left_x; curr_y <= left_y; end
                            2'b01: begin curr_x <= straight_x; curr_y <= straight_y; end
                            2'b11: begin current_dir <= right_dir(current_dir); curr_x <= right_x; curr_y <= right_y; end
                        endcase
                    end
                    else begin
                        push_to_stack <= 1'b0;
                    end
                end
                else if (phase == PHASE_GO_TO_EXIT) begin
                    if (move != MOVE_IDLE && exit_path_index < exit_path_length) begin
                        current_dir <= target_dir_peek;
                        // Notice: Position is not tracked here anymore. It's irrelevant for the speed run.
                        exit_path_index <= exit_path_index + 6'd1;
                    end
                end
            end
        end
    end
endmodule