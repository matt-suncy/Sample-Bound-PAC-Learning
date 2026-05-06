import { useMemo, useCallback } from 'react'
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

function buildLayout() {
  const visibleNodes = theoremNodes.filter(n => !EXCLUDED_FILES.has(n.file))
  const visibleIds = new Set(visibleNodes.map(n => n.id))
  const visibleEdges = theoremEdges.filter(
    e => visibleIds.has(e.source) && visibleIds.has(e.target)
  )

  const g = new dagre.graphlib.Graph()
  g.setDefaultEdgeLabel(() => ({}))
  g.setGraph({
    rankdir: 'BT',    // main theorem at TOP, leaf lemmas at BOTTOM
    ranksep: 110,
    nodesep: 45,
    marginx: 60,
    marginy: 60,
  })

  visibleNodes.forEach(n => {
    g.setNode(n.id, { width: NODE_WIDTH, height: NODE_HEIGHT_COLLAPSED })
  })
  visibleEdges.forEach(e => {
    g.setEdge(e.source, e.target)
  })

  dagre.layout(g)

  const nodes: Node<TheoremNodeData>[] = visibleNodes.map(n => {
    const pos = g.node(n.id)
    return {
      id: n.id,
      type: 'theoremNode',
      position: {
        x: pos.x - NODE_WIDTH / 2,
        y: pos.y - NODE_HEIGHT_COLLAPSED / 2,
      },
      data: n,
    }
  })

  const edges: Edge[] = visibleEdges.map((e, i) => ({
    id: `e-${i}`,
    source: e.source,
    target: e.target,
    // sourceHandle top → targetHandle bottom: arrows exit source's top, enter target's bottom
    sourceHandle: undefined,
    targetHandle: undefined,
    type: 'smoothstep',
    style: { stroke: '#111111', strokeWidth: 1 },
    markerEnd: {
      type: MarkerType.ArrowClosed,
      color: '#111111',
      width: 12,
      height: 12,
    },
  }))

  return { nodes, edges }
}

interface DependencyGraphProps {
  onNodeClick: (node: TheoremNodeData) => void
}

export default function DependencyGraph({ onNodeClick }: DependencyGraphProps) {
  const { nodes, edges } = useMemo(buildLayout, [])

  const handleNodeClick: NodeMouseHandler = useCallback(
    (_event, node) => {
      onNodeClick(node.data as TheoremNodeData)
    },
    [onNodeClick]
  )

  return (
    <ReactFlow
      nodes={nodes}
      edges={edges}
      nodeTypes={nodeTypes}
      onNodeClick={handleNodeClick}
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
