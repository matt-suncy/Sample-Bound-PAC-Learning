import { useMemo, useCallback, useState } from 'react'
import ReactFlow, {
  Background,
  Controls,
  MiniMap,
  MarkerType,
  type Node,
  type Edge,
  type NodeTypes,
  type NodeMouseHandler,
} from 'reactflow'
import dagre from '@dagrejs/dagre'
import 'reactflow/dist/style.css'

import TheoremNode, { NODE_WIDTH, NODE_HEIGHT_COLLAPSED } from './TheoremNode'
import { theoremNodes, theoremEdges, type TheoremNodeData } from '../data/graphData'

const nodeTypes: NodeTypes = { theoremNode: TheoremNode }

// Files excluded from the dependency graph (too many utility nodes, clutters the view).
// Remove a file from this set to show its nodes again.
const EXCLUDED_FILES = new Set(['Hypergeometric.lean', 'Definitions.lean'])

// Layout constants
const H_GAP = 100          // horizontal gap between nodes within a row
const RANK_SPACING = 340   // vertical distance between logical ranks
const SUBROW_SPACING = 200 // vertical distance between sub-rows within a rank
const MAX_PER_ROW = 5      // max nodes per row before splitting into a sub-row

function buildLayout() {
  const visibleNodes = theoremNodes.filter(n => !EXCLUDED_FILES.has(n.file))
  const visibleIds = new Set(visibleNodes.map(n => n.id))
  const visibleEdges = theoremEdges.filter(
    e => visibleIds.has(e.source) && visibleIds.has(e.target)
  )

  // Run dagre solely for rank assignment and crossing-minimised x ordering
  const g = new dagre.graphlib.Graph()
  g.setDefaultEdgeLabel(() => ({}))
  g.setGraph({ rankdir: 'BT', ranksep: 100, nodesep: NODE_WIDTH + 40, marginx: 60, marginy: 60 })
  visibleNodes.forEach(n => g.setNode(n.id, { width: NODE_WIDTH, height: NODE_HEIGHT_COLLAPSED }))
  visibleEdges.forEach(e => g.setEdge(e.source, e.target))
  dagre.layout(g)

  const dp = new Map(visibleNodes.map(n => [n.id, g.node(n.id)]))

  // Group nodes by rank (dagre y value, ascending → main theorem first in BT)
  const uniqueRankYs = [...new Set(visibleNodes.map(n => dp.get(n.id)!.y))].sort((a, b) => a - b)
  const yToRankIdx = new Map(uniqueRankYs.map((y, i) => [y, i]))

  const rankGroups = new Map<number, string[]>()
  visibleNodes.forEach(n => {
    const ri = yToRankIdx.get(dp.get(n.id)!.y)!
    if (!rankGroups.has(ri)) rankGroups.set(ri, [])
    rankGroups.get(ri)!.push(n.id)
  })

  // Preserve dagre's x ordering within each rank (it minimises edge crossings)
  rankGroups.forEach(ids => ids.sort((a, b) => dp.get(a)!.x - dp.get(b)!.x))

  // Assign final positions — ranks with > MAX_PER_ROW nodes split into sub-rows
  const finalPos = new Map<string, { x: number; y: number }>()
  let currentY = 0

  for (let ri = 0; ri < uniqueRankYs.length; ri++) {
    const ids = rankGroups.get(ri) ?? []
    const numSubRows = Math.ceil(ids.length / MAX_PER_ROW)

    for (let sr = 0; sr < numSubRows; sr++) {
      const slice = ids.slice(sr * MAX_PER_ROW, (sr + 1) * MAX_PER_ROW)
      const totalW = slice.length * NODE_WIDTH + (slice.length - 1) * H_GAP
      const startX = -totalW / 2
      slice.forEach((id, col) => {
        finalPos.set(id, {
          x: startX + col * (NODE_WIDTH + H_GAP),
          y: currentY + sr * SUBROW_SPACING,
        })
      })
    }
    currentY += (numSubRows - 1) * SUBROW_SPACING + RANK_SPACING
  }

  const nodes: Node<TheoremNodeData>[] = visibleNodes.map(n => ({
    id: n.id,
    type: 'theoremNode',
    position: finalPos.get(n.id)!,
    data: n,
  }))

  const edges: Edge[] = visibleEdges.map((e, i) => ({
    id: `e-${i}`,
    source: e.source,
    target: e.target,
    sourceHandle: undefined,
    targetHandle: undefined,
    type: 'smoothstep',
    style: { stroke: '#555555', strokeWidth: 1.2 },
    markerEnd: {
      type: MarkerType.ArrowClosed,
      color: '#555555',
      width: 10,
      height: 10,
    },
  }))

  return { nodes, edges }
}

interface DependencyGraphProps {
  onNodeClick: (node: TheoremNodeData) => void
}

export default function DependencyGraph({ onNodeClick }: DependencyGraphProps) {
  const { nodes, edges: baseEdges } = useMemo(buildLayout, [])
  const [hoveredNodeId, setHoveredNodeId] = useState<string | null>(null)

  // Elevate and highlight edges whose source node is currently hovered
  const edges = useMemo(
    () => baseEdges.map(e => {
      const active = e.source === hoveredNodeId
      return {
        ...e,
        zIndex: active ? 1000 : 0,
        style: { stroke: active ? '#111111' : '#555555', strokeWidth: active ? 2 : 1.2 },
        markerEnd: { type: MarkerType.ArrowClosed, color: active ? '#111111' : '#555555', width: 10, height: 10 },
      }
    }),
    [baseEdges, hoveredNodeId]
  )

  const handleNodeClick: NodeMouseHandler = useCallback(
    (_event, node) => onNodeClick(node.data as TheoremNodeData),
    [onNodeClick]
  )

  const handleNodeMouseEnter: NodeMouseHandler = useCallback(
    (_event, node) => setHoveredNodeId(node.id),
    []
  )

  const handleNodeMouseLeave: NodeMouseHandler = useCallback(
    () => setHoveredNodeId(null),
    []
  )

  return (
    <ReactFlow
      nodes={nodes}
      edges={edges}
      nodeTypes={nodeTypes}
      onNodeClick={handleNodeClick}
      onNodeMouseEnter={handleNodeMouseEnter}
      onNodeMouseLeave={handleNodeMouseLeave}
      fitView
      fitViewOptions={{ padding: 0.12 }}
      minZoom={0.04}
      maxZoom={2}
      attributionPosition="bottom-left"
      style={{ background: '#FAFAFA' }}
    >
      <Background color="#d4d4d4" gap={32} size={1} />
      <Controls style={{ border: '1px solid #888' }} />
      <MiniMap
        nodeColor={(n) =>
          (n.data as TheoremNodeData).isHighlighted ? '#8899cc' : '#555555'
        }
        nodeStrokeColor="#111111"
        nodeStrokeWidth={2}
        nodeBorderRadius={0}
        maskColor="rgba(180,180,180,0.5)"
        style={{
          border: '1px solid #555555',
          background: '#cccccc',
        }}
      />
    </ReactFlow>
  )
}
