-- DataType: Matrix
-- Created by: Dynamo (@Roller_Bott)
-- Date: 4/18/25
-- these notes keep me sane

-- Matrix Class Library
local matrix = {}
local className = "Matrix"

--// TYPE DEFINITIONS

-- The coordinates of a point in (x,y) format
type coordinates = {
	X: number;
	Y: number;
}

-- A point in the matrix
type point = {
	Value: number;
	Position: coordinates;
}

-- A row in the matrix
type row = {point}

type range = { -- Instead of NumberRange, so that module is compatible with normal lua
	A: number; -- (Size: columns)
	B: number; -- (Size: rows)
}

-- The matrix
export type Matrix = {
	-- ClassName
	ClassName: string; -- read only

	-- The size of the matrix (rows, columns)
	Size: range;

	-- The contents of the matrix itself
	Contents: {[number]: row};

	-- Insert a new point into the matrix at (column, row) or (x,y)
	assign: (self: Matrix, column: number, row: number, value: number) -> (Matrix);
	flood: (self: Matrix, value: {number}) -> (Matrix);
	fill: (self: Matrix, value: number) -> (Matrix);
	replace: (self: Matrix, replace: number, value: number) -> (Matrix);
	transpose: (self: Matrix) -> (Matrix);
	getDeterminant: (self: Matrix) -> (number);
	getRank: (self: Matrix) -> (number);
	getArea: (self: Matrix) -> (number);
	getDimensions: (self: Matrix) -> (number, number);
	getInverse: (self: Matrix) -> (Matrix);
	getTrace: (self: Matrix) -> (number);
	getIdentity: (self: Matrix) -> (Matrix);
	--getRowsOrthonormalized: (self: Matrix) -> (Matrix);
	Zero: (self: Matrix) -> (Matrix);
	One: (self: Matrix) -> (Matrix);
	isSymmetric: (self: Matrix) -> (boolean);
	isAntiSymmetric: (self: Matrix) -> (boolean);
	isSingular: (self: Matrix) -> (boolean);
	isInvertible: (self: Matrix) -> (boolean);
}

-- HELPFUL FUNCTIONS

local properties = {
	"ClassName",
	"Size",
	"Contents",
	"assign",
	"flood",
	"fill",
	"replace",
	"transpose",
	"getDeterminant",
	"getRank",
	"getArea",
	"getDimensions",
	"getInverse",
	"getTrace",
	"getIdentity",
	"Zero",
	"One",
	"isSymmetric",
	"isSingular",
	"isInvertible",
}

local allowedTypes = {
	"number",
	"table"
}

local function roundToDigits(value: number, digits: number, text)
	local startdigits = #tostring(math.floor(math.abs(value)))
	local decimals = math.max(0, digits - startdigits - 1) -- The 1 is to account for the '.' so the matrix looks pretty
	local mult = 10^decimals
	--print(value, math.floor(value*mult+0.5)/mult)
	local rounded = math.floor(value*mult+0.5)/mult

	if text then
		return string.format("%."..decimals.."f", rounded)
	else
		return rounded
	end
end

local function cloneMatrix(oldmatrix: Matrix)
	local copy: Matrix = {}
	copy.Size = {}
	copy.Size.A = oldmatrix.Size.A
	copy.Size.B = oldmatrix.Size.B
	copy.ClassName = className
	copy.Contents = {}

	for i, row: row in oldmatrix.Contents do
		copy.Contents[i] = {}

		for j, point: point in row do
			copy.Contents[i][j] = point
		end
	end

	return copy :: Matrix -- raw and without metamethods
end

local function createIdentityMatrix(n: number) --The one with all the ones and zeros
	local identity: Matrix = {} -- n x n
	identity.Size = {}
	identity.Size.A = n
	identity.Size.B = n
	identity.ClassName = className
	identity.Contents = {}

	for i=1, n, 1 do
		identity.Contents[i] = {} :: row
		for j=1, n, 1 do
			identity.Contents[i][j] = {} :: point
			identity.Contents[i][j].Value = (i == j) and 1 or 0 -- Just learned about this. It's pretty neat!
		end
	end

	setmetatable(identity, {
		__index = matrix;
	})

	return identity :: Matrix
end

local function invertMatrix(oldmatrix: Matrix) -- Gauss-Jordan Matrix Inversion (this stuff is useful, but I am going to have an aneurysm trying to code it)
	local mclone: Matrix = cloneMatrix(oldmatrix)
	local msize: range = {["A"] = oldmatrix.Size.A, ["B"] = oldmatrix.Size.B}
	local midentity: Matrix = createIdentityMatrix(msize.A) -- A or B doesn't matter bc it's squared

	for i=1, msize.A do
		-- Find pivot (diagonal of '1's) (One 1 per column so we can search recursively and stuff)
		local pivot_point: point = mclone.Contents[i][i]

		if pivot_point.Value == 0 then
			-- Cycle down the column
			for j = i+1, msize.A do
				if mclone[j][i].Value ~= 0 then
					-- Swap rows to have a nonzero pivot point (like an equation whatever we do to one side, we must also do to the other (identity matrix))
					mclone.Contents[i], mclone.Contents[j] = mclone.Contents[j], mclone.Contents[i]
					midentity.Contents[i], midentity.Contents[j] = midentity.Contents[j], midentity.Contents[i]
					pivot_point = mclone.Contents[i][i]
					break
				end
			end

			if pivot_point.Value == 0 then
				error("Matrix is not invertible, and thus indivisible")
			end
		end

		-- Step 2 aaaaaa
		-- Make pivot point equal to 1 by dividing every value in the row by the pivot point value
		for j = 1, msize.A do
			mclone.Contents[i][j].Value /= pivot_point.Value
			midentity.Contents[i][j].Value /= pivot_point.Value
		end

		-- Step 3 ;-; (We're almost there!)
		-- Praying this works off rip (it DID NOT work off rip ;-;)
		-- Do the math on rows that aren't on the pivot
		for k = 1, msize.A do
			if k ~= i then
				local factor = mclone.Contents[k][i].Value
				for j = 1, msize.A do
					mclone.Contents[k][j].Value -= (factor * mclone.Contents[i][j].Value)
					midentity.Contents[k][j].Value -= (factor * midentity.Contents[i][j].Value)
				end
			end
		end
	end

	for y, row: row in midentity.Contents do
		for x, point: point in row do
			point.Position = {
				["X"] = x,
				["Y"] = y
			}
		end
	end

	--print(midentity) -- OOPS! Forgot the positions somehow? aaaaa
	return midentity
end

local function transposeMatrix(oldmatrix: Matrix) -- Basically rotate it
	local newMatrix: Matrix = {}
	newMatrix.Size = {}
	newMatrix.Size.A = oldmatrix.Size.B
	newMatrix.Size.B = oldmatrix.Size.A
	newMatrix.ClassName = className
	newMatrix.Contents = {}

	for i=1, oldmatrix.Size.A, 1 do
		newMatrix.Contents[i] = {}
		for j=1, oldmatrix.Size.B, 1 do
			newMatrix.Contents[i][j] = oldmatrix.Contents[j][i]
		end
	end

	return newMatrix :: Matrix
end

local function dotProduct(a, b)
	local sum = 0
	print(a, b)
	for i=1, #a do
		sum += a[i].Value * b[i].Value
	end
	return sum
end

local function subtractVectors(a,b)
	local result = {}
	for i= 1, #a do
		result[i] = a[i].Value - b[i].Value
	end
	
	return result
end

local function scaleVector(vectr, scalar)
	local result: row = {}
	for i = 1, #vectr do
		local newPoint: point = {}
		newPoint.Value, newPoint.Position = {}, {}
		newPoint.Value = vectr[i].Value * scalar
		newPoint.Position.X = vectr[i].Position.X
		newPoint.Position.Y = vectr[i].Position.Y
		
		table.insert(result, newPoint.Position.X, newPoint)
	end
	
	return result
end

local function normalizeVector(vectr)
	local vector_length = math.sqrt(dotProduct(vectr, vectr))
	
	if vector_length == 0 then error("Attempt to normalize zero vector") end
	print("scale")
	return scaleVector(vectr, 1/vector_length)
end

-- Metatable Function
local function metamethods(givenmatrix: Matrix)	
	setmetatable(givenmatrix,{
		__index = matrix;

		__newindex = function(t: Matrix, key: number, value: number)
			if key == "ClassName" or key == "Size" or key == "Contents" then
				error("Unable to assign property "..tostring(key)..". Property is read only")
			else
				error("Unable to assign property "..tostring(key)..". Property does not exist")
			end
		end;

		__len = function(t: Matrix)
			local points = 0

			for i, row: row in t.Contents do
				points += #row
			end

			return points
		end;

		__metatable = "Matrix";

		__call = function(t: Matrix)
			for i, row: row in t.Contents do
				for i, point: point in row do
					print("("..tostring(point.Position.X)..", "..tostring(point.Position.Y).."): "..tostring(point.Value))
				end
			end
		end;

		__concat = function(t: Matrix, value)
			local writtenTable = {}
			local mostdigits = 0

			for i=1, t.Size.B, 1 do
				for j, point in t.Contents[i] do
					if string.len(tostring(point.Value)) > mostdigits then mostdigits = string.len(tostring(point.Value)); end
				end
			end

			for i=1, t.Size.B, 1 do
				local currentRow = t.Contents[i]
				local values = {}

				for j, point in currentRow do
					table.insert(values, point.Position.X, roundToDigits(point.Value, mostdigits, true))
				end

				writtenTable[i] = table.concat(values, ", ")

			end

			local resultant = ""

			for i, row in writtenTable do
				if i == 1 then
					resultant = resultant.."\n? "..row.." ?\n"

				elseif i == #writtenTable then
					resultant = resultant.."\n? "..row.." ?\n"

				else
					resultant = resultant.."\n| "..row.." |\n"
				end

				--resultant = resultant.."\n[ "..row.." ]\n"
			end

			return resultant
		end;

		__tostring = function(t: Matrix)
			local writtenTable = {}
			local mostdigits = 0

			for i=1, t.Size.B, 1 do
				for j, point in t.Contents[i] do
					if string.len(tostring(point.Value)) > mostdigits then mostdigits = string.len(tostring(point.Value)); end
				end
			end

			for i=1, t.Size.B, 1 do
				local currentRow = t.Contents[i]
				local values = {}

				--print(mostdigits)
				for j, point in currentRow do
					table.insert(values, point.Position.X, roundToDigits(point.Value, mostdigits, true))
				end

				writtenTable[i] = table.concat(values, ", ")
			end

			local resultant = ""

			for i, row in writtenTable do
				if i == 1 then
					resultant = resultant.."\n? "..row.." ?\n"

				elseif i == #writtenTable then
					resultant = resultant.."\n? "..row.." ?\n"

				else
					resultant = resultant.."\n| "..row.." |\n"
				end

				--resultant = resultant.."\n[ "..row.." ]\n"
			end

			return resultant
		end;

		__unm = function(t: Matrix)
			for i=1, t.Size.B, 1 do

				for j, point in t.Contents[i] do
					point.Value *= -1
				end
			end

			return t :: Matrix
		end;

		__add = function(t: Matrix, value)
			if table.find(allowedTypes, type(value)) then
				if type(value) == "number" then
					for i=1, t.Size.B, 1 do

						for j, point in t.Contents[i] do
							point.Value += value
						end
					end

					return t :: Matrix

				elseif getmetatable(value) == "Matrix" then
					if value.Contents and value.Size then
						if value.Size.A == t.Size.A and value.Size.B == t.Size.B then
							for i=1, t.Size.B, 1 do

								for j, point in t.Contents[i] do
									point.Value += value.Contents[i][j].Value
								end
							end

							return t :: Matrix
						else
							error("Terminated attempt to perform arithmetic between Matrices of different proportions")
						end
					else
						error("Attempt to perform arithmetic on malformed Matrix")
					end
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end
		end;

		__sub = function(t: Matrix, value)
			if table.find(allowedTypes, type(value)) then
				if type(value) == "number" then
					for i=1, t.Size.B, 1 do

						for j, point in t.Contents[i] do
							point.Value -= value
						end
					end

					return t :: Matrix

				elseif getmetatable(value) == "Matrix" then
					if value.Contents and value.Size then
						if value.Size.A == t.Size.A and value.Size.B == t.Size.B then
							for i=1, t.Size.B, 1 do

								for j, point in t.Contents[i] do
									point.Value -= value.Contents[i][j].Value
								end
							end

							return t :: Matrix
						else
							error("Terminated attempt to perform arithmetic between Matrices of different proportions")
						end
					else
						error("Attempt to perform arithmetic on malformed Matrix")
					end
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end
		end;

		__mul = function(t: Matrix, value)
			if table.find(allowedTypes, type(value)) then
				if type(value) == "number" then
					for i=1, t.Size.B, 1 do

						for j, point in t.Contents[i] do
							point.Value *= value
						end
					end

					return t :: Matrix

				elseif getmetatable(value) == "Matrix" then
					if value.Contents and value.Size then
						if t.Size.A == value.Size.B then
							local resultMatrix: Matrix = {}
							resultMatrix.Size = {}
							resultMatrix.Contents = {}
							resultMatrix.ClassName = className

							for i=1, t.Size.A do
								local currentRow = t.Contents[i]

								for j = 1, value.Size.B, 1 do
									local sum = 0

									for k = 1, t.Size.A, 1 do
										--print(t.Size, value.Size)
										--print(t)
										----print(t)
										--print(value.Contents[k], k)
										sum += currentRow[k].Value * value.Contents[k][j].Value
									end
									--currentRow[j].Value = sum
									-- need a result matrix
									if not(resultMatrix.Contents[i]) then resultMatrix.Contents[i] = {} :: row end
									if not(resultMatrix.Contents[i][j]) then
										resultMatrix.Contents[i][j] = {} :: point
										resultMatrix.Contents[i][j].Value = sum
										resultMatrix.Contents[i][j].Position = {
											["X"] = j;
											["Y"] = i;
										}
									end

									resultMatrix.Size.A = t.Size.A
									resultMatrix.Size.B = value.Size.B
								end

							end

							return metamethods(resultMatrix) :: Matrix

						else
							error("Terminated attempt to perform arithmetic between Matrices of different proportions (#Rows ~= #Columns)")
						end
					else
						error("Attempt to perform arithmetic on malformed Matrix")
					end
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end
		end;

		__div = function(t: Matrix, value)
			if table.find(allowedTypes, type(value)) then
				if type(value) == "number" then
					for i=1, t.Size.B, 1 do

						for j, point in t.Contents[i] do
							point.Value /= value
						end
					end

					return t :: Matrix

				elseif getmetatable(value) == "Matrix" then
					if value.Contents and value.Size then
						-- multiply the left matrix by the inverse of the right matrix [table * inverse(value)]
						if t.Size.A == value.Size.A then -- bc it will be the inverse size that has to be equal
							if value.Size.A == value.Size.B then -- Do Gauss-Jordan
								local invertedMatrix: Matrix = metamethods(invertMatrix(value))
								local quotient: Matrix = t * invertedMatrix
								return quotient :: Matrix

							else -- Maybe try using Moore-Penrose sometime ;-;
								-- I don't completely understand WHY it works (like all the math behind this equation), but I do know that it works so I'll use it
								-- Have to do pseudoinversion here bc metamethods are needed

								local matrix_t: Matrix = metamethods(transposeMatrix(value)) -- To get full row/column rank

								if value.Size.B >= value.Size.A then -- If #rows >= #columns (tall) [Order matters]
									-- inverse(matrix_t*matrix) * matrix_t = matrix_pseudoinverse
									-- matrix_t*matrix aka Mt * M aka MtM
									local MtM: Matrix = matrix_t*matrix
									local invMtM = metamethods(invertMatrix(MtM))

									return invMtM*matrix_t :: Matrix

								else -- If #columns > #rows (wide)
									-- matrix_t * inverse(matrix_t*matrix) = matrix_pseudoinverse
									-- matrix*matrix_t aka M * Mt aka Mt
									local MMt: Matrix = matrix*matrix_t
									local invMMt: Matrix = metamethods(invertMatrix(MMt))

									return matrix_t*invMMt :: Matrix

								end


								--error("Terminated attempt to divide by a non-square Matrix") (Unreachable code)
							end
						else
							error("Terminated attempt to perform arithmetic between Matrices of different proportions (#Rows ~= #Columns)")
						end

					else
						error("Attempt to perform arithmetic on malformed Matrix")
					end
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end
		end;

		__idiv = function(t:Matrix, value)
			if table.find(allowedTypes, type(value)) then
				if type(value) == "number" then
					for i=1, t.Size.B, 1 do

						for j, point in t.Contents[i] do
							point.Value //= value
						end
					end

					return t :: Matrix

				elseif getmetatable(value) == "Matrix" then
					if value.Contents and value.Size then
						-- multiply the left matrix by the inverse of the right matrix [table * inverse(value)]
						if t.Size.A == value.Size.A then -- bc it will be the inverse size that has to be equal
							if value.Size.A == value.Size.B then -- Do Gauss-Jordan
								local invertedMatrix: Matrix = metamethods(invertMatrix(value))
								local quotient: Matrix = t * invertedMatrix

								for y, row: row in quotient.Contents do
									for x, point: point in row do
										--print(point.Value, math.round(point.Value))
										point.Value = roundToDigits(point.Value, string.len(tostring(point.Value)))
										if point.Value == 0 then point.Value = 0 end -- prevent -0
									end
								end

								return quotient :: Matrix

							else -- Maybe try using Moore-Penrose sometime ;-;
								-- I don't completely understand WHY it works (like all the math behind this equation), but I do know that it works so I'll use it
								-- Have to do pseudoinversion here bc metamethods are needed

								local matrix_t: Matrix = metamethods(transposeMatrix(value)) -- To get full row/column rank

								if value.Size.B >= value.Size.A then -- If #rows >= #columns (tall) [Order matters]
									-- inverse(matrix_t*matrix) * matrix_t = matrix_pseudoinverse
									-- matrix_t*matrix aka Mt * M aka MtM
									local MtM: Matrix = matrix_t*matrix
									local invMtM = metamethods(invertMatrix(MtM))

									local raw_matrix: Matrix = invMtM*matrix_t

									for y, row: row in raw_matrix.Contents do
										for x, point: point in row do
											--print(point.Value, math.round(point.Value))
											point.Value = roundToDigits(point.Value, string.len(tostring(point.Value)))

										end
									end

									return raw_matrix

								else -- If #columns > #rows (wide)
									-- matrix_t * inverse(matrix_t*matrix) = matrix_pseudoinverse
									-- matrix*matrix_t aka M * Mt aka Mt
									local MMt: Matrix = matrix*matrix_t
									local invMMt: Matrix = metamethods(invertMatrix(MMt))

									local raw_matrix: Matrix = matrix_t*invMMt

									for y, row: row in raw_matrix.Contents do
										for x, point: point in row do
											--print(point.Value, math.round(point.Value))
											point.Value = roundToDigits(point.Value, string.len(tostring(point.Value)))
										end
									end

									return raw_matrix

								end


								--error("Terminated attempt to divide by a non-square Matrix") (Unreachable code)
							end
						else
							error("Terminated attempt to perform arithmetic between Matrices of different proportions (#Rows ~= #Columns)")
						end

					else
						error("Attempt to perform arithmetic on malformed Matrix")
					end
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end
		end;

		__mod = function(t: Matrix, value)
			if type(value) == "number" then
				for y, row: row in t.Contents do
					for x, point: point in row do
						point.Value = point.Value%value
					end
				end

				return t :: Matrix

			elseif getmetatable(value) == "Matrix" then
				if value.Size and value.Contents then
					if (value.Size.A == t.Size.A) and (value.Size.B == t.Size.B) then
						for y, row: row in t.Contents do
							for x, point: point in row do
								point.Value %= value.Contents[y][x].Value
							end
						end

						return t :: Matrix

					else
						error("Attempt to perform modulus operation on Matrix of size "..t.Size.A.."x"..t.Size.B.." and Matrix of size "..value.Size.A.."x"..value.Size.B)
					end
				else
					error("Attempt to perform arithmetic on malformed Matrix")
				end
			else
				error("Attempt to perform arithmetic between Matrix and "..type(value))
			end

		end;

		__pow = function(t: Matrix, value)
			if type(value) == "number" then
				local base: Matrix = t

				if t.Size.A == t.Size.B then
					for i=1, value, 1 do
						t *= base
					end

					return t :: Matrix
				else
					error("Attempt to raise Matrix of non-square proportions to an exponent")
				end
			else
				error("Attempt to raise Matrix to non-scalar exponent")
			end
		end;

		__eq = function(t:Matrix, value)
			if type(value) == "number" then
				for y, row: row in t.Contents do
					for x, point: point in row do
						if point.Value ~= value then
							return false
						end
					end
				end

				return true

			elseif getmetatable(value) == "Matrix" then
				if value.Size and value.Contents then
					if value.Size.A == t.Size.A and value.Size.B == t.Size.B then
						for y, row: row in t.Contents do
							for x, point: point in row do
								if point.Value ~= value.Contents[y][x].Value then
									return false
								end
							end
						end

						return true

					else
						error("Attempt to compare nonsimilar Matrices")
					end
				else
					error("Attempt to index a malformed Matrix")
				end

			else
				error("Attempt to index Matrix and "..type(value))
			end
		end;

		__lt = function(t:Matrix, value)
			if type(value) == "number" then
				for y, row: row in t.Contents do
					for x, point: point in row do
						if not(point.Value < value) then
							return false
						end
					end
				end

				return true

			elseif getmetatable(value) == "Matrix" then
				if value.Size and value.Contents then
					if value.Size.A == t.Size.A and value.Size.B == t.Size.B then
						for y, row: row in t.Contents do
							for x, point: point in row do
								if not(point.Value < value.Contents[y][x].Value) then
									return false
								end
							end
						end

						return true

					else
						error("Attempt to compare nonsimilar Matrices")
					end
				else
					error("Attempt to index a malformed Matrix")
				end

			else
				error("Attempt to index Matrix and "..type(value))
			end
		end;

		__le = function(t:Matrix, value)
			if type(value) == "number" then
				for y, row: row in t.Contents do
					for x, point: point in row do
						if not(point.Value <= value) then
							return false
						end
					end
				end

				return true

			elseif getmetatable(value) == "Matrix" then
				if value.Size and value.Contents then
					if value.Size.A == t.Size.A and value.Size.B == t.Size.B then
						for y, row: row in t.Contents do
							for x, point: point in row do
								if not(point.Value <= value.Contents[y][x].Value) then
									return false
								end
							end
						end

						return true

					else
						error("Attempt to compare nonsimilar Matrices")
					end
				else
					error("Attempt to index a malformed Matrix")
				end

			else
				error("Attempt to index Matrix and "..type(value))
			end
		end;

		__iter = function(t: Matrix)
			local points = {}

			for y, row: row in t.Contents do
				for x, point: point in row do
					points[point.Position.X..", "..point.Position.Y] = point.Value
				end
			end

			return pairs(points)
		end;

	})

	return givenmatrix
end

local function findDeterminant(t: Matrix) -- for recursive searching
	if t.Size.A == 1 then
		return t.Contents[1][1].Value
	elseif t.Size.A == 2 then
		return t.Contents[1][1].Value*t.Contents[2][2].Value - t.Contents[1][2].Value*t.Contents[2][1].Value
	else
		-- Using Cramer's Rule
		local det = 0

		for column = 1, t.Size.A, 1 do
			local minor = {}
			minor.Contents = {} :: {row}
			minor.Size = {} :: range
			minor.ClassName = className

			for i = 2, t.Size.A do
				minor.Contents[i - 1] = {}
				for j = 1, t.Size.A do
					if j ~= t.Size.A then
						table.insert(minor.Contents[i - 1], t.Contents[i][j])
					end
				end
			end

			minor.Size.A = #minor.Contents[1]
			minor.Size.B = #minor.Contents

			minor = metamethods(minor)

			local sign = ((column % 2 == 1) and 1) or -1
			det += sign * t.Contents[1][column].Value * findDeterminant(minor)
		end
		return det
	end
end

local function newRow(currentrow:number, columns: number, defaultvalue: number): row
	local row: row = {}

	for i=1, columns, 1 do
		local temporary_point:point = {
			["Value"] = defaultvalue;
			["Position"] = {
				["X"] = i,
				["Y"] = currentrow
			}
		}

		setmetatable(temporary_point, {
			__index = function(t: point, key)
				--print(key)

				if string.lower(key) == "value" then
					return rawget(t, "Value")

				elseif string.lower(key) == "position" then
					return rawget(t, "Position")

				elseif string.lower(key) == "x" or string.lower(key) == "column" then
					return rawget(t, "Position").X

				elseif string.lower(key) == "y" or string.lower(key) == "row" then
					return rawget(t, "Position").Y

				else
					warn(key.." is not a property of the 'point' class. Returning "..t.Value.." in its place...")
					return t.Value
				end
			end;

			__newindex = function(t: point, key, value)
				error(key.." is not a valid member of the 'point' class")
			end;

		})

		row[i] = temporary_point
	end

	return row :: row
end


matrix.__index = matrix

-- VARIABLES
local empty: range = {
	Maximum = 0, Minimum = 0
}

-- CONSTRUCTOR

-- Create a new empty matrix. Without default value, the default value is set equal to 0.
function matrix.new(columns: number, rows: number, defaultvalue: number): Matrix
	local self = setmetatable({}, matrix) :: Matrix

	assert(columns > 0, "Attempt to define #columns as a non-natural number")
	assert(rows > 0, "Attempt to define #rows as a non-natural number")

	if not(defaultvalue) then defaultvalue = 0; end

	self.ClassName = className
	self.Size = {
		["A"] = columns;
		["B"] = rows;
	}

	self.Contents = {}

	for i=1, rows, 1 do
		self.Contents[i] = newRow(i, columns, defaultvalue)
	end
	--print(self)

	return metamethods(self)
end

-- OBJECT METHODS

function matrix:fill(value: number)
	for y, row: row in self.Contents do
		for x, point: point in row do
			point.Value = value
		end
	end

	return self
end

function matrix:flood(value: {number})

	if self.Size.A*self.Size.B == #value then
		local index = 1
		for y, row: row in self.Contents do
			for x, point: point in row do
				point.Value = value[index]
				index += 1
			end
		end
		
		return self
	else
		error("Number of values in table does not match number of values in Matrix")
	end
end

function matrix:getArea()
	return self.Size.A*self.Size.B
end

function matrix:getInverse()

		if self.Size.A == self.Size.B then
			local invertedMatrix: Matrix = metamethods(invertMatrix(self))
			return invertedMatrix
		else

			local matrix_t: Matrix = metamethods(transposeMatrix(self))

			if self.Size.B >= self.Size.A then

				local MtM: Matrix = matrix_t*matrix
				local invMtM = metamethods(invertMatrix(MtM))

				return invMtM

			else

				local MMt: Matrix = matrix*matrix_t
				local invMMt: Matrix = metamethods(invertMatrix(MMt))

				return invMMt

			end
		end
end

function matrix:getDimensions()
	return self.Size.A, self.Size.B
end

function matrix:replace(replace: number, value: number)
	for y, row: row in self.Contents do
		for x, point: point in row do
			if point.Value == replace then
				point.Value = value
			end
		end
	end

	return self
end

function matrix:getDeterminant() -- Recursive searching may cause lag with large matrices
	return findDeterminant(self)
end

function matrix:transpose()
	local newMatrix = metamethods(transposeMatrix(self))
	return newMatrix :: Matrix
end

function matrix:getRank()
	local rank = 0

	local init = 1

	for x = 1, self.Size.A do
		local pivot_row -- Row w/ first non-zero entry (pivot element)
		for y = init, self.Size.B do
			if math.abs(self.Contents[x][y].Value) > 1e-10 then
				pivot_row = x
				break
			end
		end

		if pivot_row then
			self.Contents[init], self.Contents[pivot_row] = self.Contents[pivot_row], self.Contents[init]

			-- just learned this is called normalization
			local pivot = self.Contents[init][x].Value

			for column = x, self.Size.A do
				self.Contents[init][column].Value /= pivot
			end

			for row = init+1, self.Size.B do -- Start at next row
				local factor = self.Contents[row][x].Value
				for column = x, self.Size.A do
					self.Contents[row][column].Value -= factor*self.Contents[init][column].Value
				end
			end

			rank += 1
			init += 1
		end
	end

	return rank
end

function matrix:getTrace()
	if self.Size.A == self.Size.B then
		local total = 0
		
		for y, row: row in self.Contents do
			total += row[y].Value
		end
		
		return total
	else
		error("Attempt to retrieve trace of a non-square Matrix")
	end
end

-- Insert a new point of a defined value into the matrix at (column, row) aka (x,y)
function matrix:assign(column: number, row: number, value: number)
	assert(value ~= nil, "Value is set to nil")
	assert(column ~= nil, "Column is set to nil")
	assert(row ~= nil, "Row is set to nil")
	--print(self.Size, row)
	--assert(self.Size.A >= column, "Column "..column.." does not exist in "..self) <- SOMEHOW MAKES SIZE == nil
	--assert(self.Size.B >= row, "Row "..row.." does not exist in "..self) <- SOMEHOW MAKES SIZE == nil

	assert(column > 0, "Attempt to insert value in column at a non-natural number")
	assert(row > 0, "Attempt to insert value in row at a non-natural number")

	self.Contents[row][column].Value = value

	return self
end

function matrix:Zero()
	local newMatrix = matrix.new(self.Size.A, self.Size.B, 0)
	return newMatrix
end

function matrix:One()
	local newMatrix = matrix.new(self.Size.A, self.Size.B, 1)
	return newMatrix
end

function matrix:getIdentity()
	if self.Size.A == self.Size.B then
		local identityMatrix = matrix.new(self.Size.A, self.Size.B, 0)
		
		for y, row: row in self.Contents do
			for x, point: point in row do
				if x == y then
					identityMatrix.Contents[y][x].Value = 1
				end
			end
		end

		return identityMatrix
	else
		error("Attempt to create identity of a non-square Matrix")
	end
end

function matrix:getDiagonal()
	if self.Size.A == self.Size.B then
		local diagonalMatrix = matrix.new(self.Size.A, self.Size.B, 0)

		for y, row: row in self.Contents do
			for x, point: point in row do
				if x == y then
					diagonalMatrix.Contents[y][x].Value = point.Value
				end
			end
		end

		return diagonalMatrix
	else
		error("Attempt to create diagonal matrix using a non-square Matrix")
	end
end

function matrix:isSymmetric()
	if self.Size.A ~= self.Size.B then return false end
	
	for y, row: row in self.Contents do
		for x, point: point in row do
			if self.Contents[x][y].Value ~= point.Value then
				return false
			end
		end
	end
	
	return true
end

function matrix:isAntiSymmetric()
	if self.Size.A ~= self.Size.B then return false end

	for y, row: row in self.Contents do
		for x, point: point in row do
			if y == x then
				if point.Value ~= 0 then
					return false
				end
			else
				if self.Contents[x][y].Value ~= -point.Value then
					return false
				end
			end
		end
	end

	return true
end

--function matrix:getRowsOrthonormalized() -- I have no idea what the math/science behind this is. I haven't taken physics yet. I'm just going based on the equations, man ;-;
--	local ortho = {}
	
--	for y = 1, #self.Contents, 1 do
--		--print("e")
--		local vi = {table.unpack(self.Contents[y])}
--		--print(vi)
--		for j = 1, #ortho do
--			--print(ortho)
--			--print("scale & dotproduct")
--			local proj = scaleVector(ortho[j], dotProduct(vi, ortho[j]))
--			--print("subtract")
--			vi = subtractVectors(vi, proj)
--		end
--		--print("normalize")
--		table.insert(ortho, normalizeVector(vi))
--		--print("Ortho: ",ortho)
--	end
	
--	local orthoMatrix: Matrix = matrix.new(self.Size.A, self.Size.B)
--	orthoMatrix:flood(ortho)
	
--	return orthoMatrix
--end

function matrix:isSingular()
	if self:getDeterminant() == 0 then
		return true
	else
		return false
	end
end

function matrix:isInvertible()
	if self:getDeterminant() == 0 then
		return false
	else
		return true
	end
end

function matrix.zero(columns: number, rows: number)
	if not(columns) or not(rows) then columns, rows = 3, 3 end
	
	local newMatrix = matrix.new(columns, rows, 0)
	return newMatrix
end

function matrix.one(columns: number, rows: number)
	if not(columns) or not(rows) then columns, rows = 3, 3 end
	
	local newMatrix = matrix.new(columns, rows, 1)
	return newMatrix
end

return matrix
